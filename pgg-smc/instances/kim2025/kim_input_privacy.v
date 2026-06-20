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
    consequence of log x <= (x - 1) log e), under absolute continuity so the
    bound also covers product references with zeros off the support.
    @composes: kim_input_private *)
Fact le_div_chi2 (T : finType) (P Q : R.-fdist T) :
  P `<< Q ->
  divergence.div P Q <= chi2_div P Q * log (sequences.expR 1).
Proof.
move=> /dominatesP PQ; rewrite /divergence.div /chi2_div.
have Hbound : divergence.div P Q <=
    (\sum_(a in T) (P a ^+ 2 / Q a - P a)) * log (sequences.expR 1).
  rewrite big_distrl /= /divergence.div.
  apply: ler_sum => a _.
  have [Pa0|PaN0] := eqVneq (P a) 0.
    by rewrite Pa0 expr0n /= mul0r !mul0r subr0 mul0r.
  have QaN0 : Q a != 0.
    by apply/negP => /eqP Qa0; rewrite (PQ a Qa0) eqxx in PaN0.
  have HPQ : 0 < P a / Q a.
    by apply: divr_gt0; rewrite lt0r ?PaN0 ?QaN0 /=; exact: FDist.ge0.
  have Hlog := log_id_cmp HPQ.
  rewrite -mulrA -[X in _ - X]mulr1 -mulrBr -mulrA.
  by apply: ler_wpM2l; [exact: FDist.ge0 | exact: Hlog].
have HR : \sum_(a in T) (P a ^+ 2 / Q a - P a) =
    (\sum_(a in T) P a ^+ 2 / Q a) - 1 by rewrite sumrB FDist.f1.
have Hterm : forall a : T, (P a - Q a) ^+ 2 / Q a =
    P a ^+ 2 / Q a - P a *+ 2 + Q a.
  move=> a.
  have [Qa0|QaN0] := eqVneq (Q a) 0; last first.
    apply: (mulIf QaN0).
    rewrite divfK // sqrrB mulrDl mulrBl divfK //.
    by rewrite mulrnAl -expr2.
  by rewrite Qa0 (PQ a Qa0) subrr expr0n /= mul0r mul0rn subr0 addr0.
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
Proof.
move=> Hx.
have F0x : x.1 && x.2 = false by apply/negbTE.
have key : forall x' : bool * bool, x'.1 && x'.2 = false ->
    \sum_v `|kim_q A x v - kim_q A x' v| <= 4%:R * `|eps|.
  move=> x' Hx'.
  apply: (order.Order.POrderTheory.le_trans
    (y := \sum_v (`|kim_q A x v - kim_qctr A x v|
               + `|kim_q A x' v - kim_qctr A x' v|))).
    apply: ler_sum => v _.
    have hctr : kim_qctr A x v = kim_qctr A x' v
      by apply: kim_qctr_eq; rewrite F0x Hx'.
    apply: (order.Order.POrderTheory.le_trans (ler_distD (kim_qctr A x v) _ _)).
    by rewrite hctr; apply: lerD => //; rewrite distrC.
  rewrite big_split /=.
  have -> : 4%:R * `|eps| = 2%:R * `|eps| + 2%:R * `|eps| by rewrite -mulrDl -natrD.
  by apply: lerD; exact: kim_q_dev.
have Henum : forall g : bool * bool -> R,
    \sum_(x' in {: bool * bool} | ~~ (x'.1 && x'.2)) g x'
    = g (false, false) + g (false, true) + g (true, false).
  move=> g; rewrite big_mkcondl /=.
  rewrite (bigD1 (false, false)) //= (bigD1 (false, true)) //=
    (bigD1 (true, false)) //=.
  rewrite big1 ?addr0; [lra | by move=> [[|] [|]]].
apply: (order.Order.POrderTheory.le_trans (y :=
  \sum_v 3%:R^-1 * (`|kim_q A x v - kim_q A (false, false) v|
                  + `|kim_q A x v - kim_q A (false, true) v|
                  + `|kim_q A x v - kim_q A (true, false) v|))).
  apply: ler_sum => v _.
  rewrite /kim_qbar (Henum (fun x' => kim_q A x' v)).
  have -> : kim_q A x v
            - 3%:R^-1 * (kim_q A (false, false) v + kim_q A (false, true) v
                       + kim_q A (true, false) v)
          = 3%:R^-1 * ((kim_q A x v - kim_q A (false, false) v)
                     + (kim_q A x v - kim_q A (false, true) v)
                     + (kim_q A x v - kim_q A (true, false) v)) by lra.
  rewrite normrM ger0_norm ?invr_ge0 ?ler0n //.
  apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
  apply: (order.Order.POrderTheory.le_trans (ler_normD _ _)).
  by rewrite lerD2r; exact: ler_normD.
rewrite -mulr_sumr !big_split /=.
apply: (order.Order.POrderTheory.le_trans (y :=
  3%:R^-1 * (4%:R * `|eps| + 4%:R * `|eps| + 4%:R * `|eps|))).
  apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
  apply: lerD; [apply: lerD|].
  - by apply: key.
  - by apply: key.
  - by apply: key.
by lra.
Qed.

(** eps_small — the input-privacy bound holds in the small-bias regime
    |eps| < 1/5, where the minimum cut weight (hence every realised conditional
    view mass) stays positive; without it the bound's denominator 1/5 - |eps|
    turns nonpositive and the inequality fails against cond_mutual_info >= 0.
    All concrete Kim instances (den Boer eps = 0, Kim bias 1/100) satisfy it. *)
Hypothesis eps_small : 0 < 5%:R^-1 - `|eps|.

(** kim_q_ge_pos — when a view is realised by some uniform cut, its biased weight
    is at least the minimum cut weight 1/5 - |eps|.
    @composes: kim_input_private *)
Fact kim_q_ge_pos (A : seq nat) (x' : bool * bool) (v : (size A).-tuple bool) :
  0 < kim_qctr A x' v -> 5%:R^-1 - `|eps| <= kim_q A x' v.
Proof.
move=> Hpos.
have Hcard : (0 < #|(fun i : 'I_5 => ViewA R A (x', i) == v)|)%N.
  rewrite lt0n; apply/negP => /eqP Hc0.
  move: Hpos; rewrite /kim_qctr sumr_const Hc0 mulr0n.
  by move=> /lt0r_neq0; rewrite eqxx.
rewrite /kim_q.
apply: (order.Order.POrderTheory.le_trans
  (y := \sum_(k in 'I_5 | ViewA R A (x', k) == v) (5%:R^-1 - `|eps|))).
  set c := (5%:R^-1 - `|eps|).
  have Hc0 : 0 <= c by rewrite /c; exact: order.Order.POrderTheory.ltW eps_small.
  rewrite sumr_const -[X in X <= _]mulr1n.
  rewrite -subr_ge0 -mulrnBr //.
  exact: mulrn_wge0.
by apply: ler_sum => k _; exact: kim_w_ge.
Qed.

(** kim_qbar_ge — when the false-fibre average view law is nonzero, it is at
    least the minimum cut weight 1/5 - |eps|.
    @composes: kim_input_private *)
Fact kim_qbar_ge (A : seq nat) (v : (size A).-tuple bool) :
  kim_qbar A v != 0 -> 5%:R^-1 - `|eps| <= kim_qbar A v.
Proof.
move=> Hbar.
have Hsum : \sum_(x in {: bool * bool} | ~~ (x.1 && x.2)) kim_q A x v != 0.
  by apply: contra Hbar => /eqP H0; rewrite /kim_qbar H0 mulr0.
move: Hsum; rewrite psumr_neq0; last by move=> i _; exact: kim_q_ge0.
move=> /hasP[x0 _] /andP[Hfib Hq0].
have Hctr0 : forall x', 0 < kim_q A x' v -> 0 < kim_qctr A x' v.
  move=> x' Hqx.
  have Hcard : (0 < #|(fun i : 'I_5 => ViewA R A (x', i) == v)|)%N.
    have Hq0' : kim_q A x' v != 0 by rewrite Num.Theory.lt0r_neq0.
    move: Hq0'; rewrite /kim_q psumr_neq0; last by move=> i _; exact: FDist.ge0.
    move=> /hasP[k _] /andP[Hk _]; apply/card_gt0P; exists k.
    by case/andP: Hk.
  rewrite /kim_qctr sumr_const pmulrn_rgt0 //.
  by rewrite invr_gt0 ltr0n.
have Hx0F : x0.1 && x0.2 = false by move: Hfib => /andP[_] /negbTE.
have Hctrx0 : 0 < kim_qctr A x0 v by exact: Hctr0.
have Hall : forall x', x'.1 && x'.2 = false -> 5%:R^-1 - `|eps| <= kim_q A x' v.
  move=> x' Hx'.
  apply: kim_q_ge_pos.
  by rewrite (kim_qctr_eq (x' := x0)) // Hx' Hx0F.
rewrite /kim_qbar.
apply: (order.Order.POrderTheory.le_trans
  (y := 3%:R^-1 * \sum_(x' in {: bool * bool} | ~~ (x'.1 && x'.2))
           (5%:R^-1 - `|eps|))).
  rewrite sumr_const.
  have Hc3 : #|(fun i : bool * bool => ~~ (i.1 && i.2))| = 3%N.
    rewrite -sum1_card.
    rewrite (bigD1 (false, false)) //= (bigD1 (false, true)) //=
      (bigD1 (true, false)) //=.
    by rewrite big1 ?addn0; [ | by move=> [[|] [|]]].
  rewrite Hc3.
  rewrite -[X in _ <= _ * X]mulr_natr; lra.
apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
apply: ler_sum => x' Hx'.
by apply: Hall; apply/negbTE.
Qed.

(** kim_qbar_sum1 — the false-fibre average view law is a probability law.
    @composes: kim_input_private *)
Fact kim_qbar_sum1 (A : seq nat) : \sum_v kim_qbar A v = 1.
Proof.
rewrite /kim_qbar -mulr_sumr exchange_big /=.
under eq_bigr => x _ do rewrite kim_qsum1.
rewrite sumr_const.
have Hc3 : #|(fun i : bool * bool => ~~ (i.1 && i.2))| = 3%N.
  rewrite -sum1_card.
  rewrite (bigD1 (false, false)) //= (bigD1 (false, true)) //=
    (bigD1 (true, false)) //=.
  by rewrite big1 ?addn0; [ | by move=> [[|] [|]]].
by rewrite Hc3 mulVf // pnatr_eq0.
Qed.

(** kim_chi2_bound — a false-fibre input's view law deviates from the mixed
    reference by chi-square at most 16 eps^2 / (1/5 - |eps|).
    @composes: kim_input_private *)
Fact kim_chi2_bound (A : seq nat) (x : bool * bool) :
  ~~ (x.1 && x.2) ->
  \sum_v (kim_q A x v - kim_qbar A v) ^+ 2 / kim_qbar A v
    <= 16%:R * eps ^+ 2 / (5%:R^-1 - `|eps|).
Proof.
move=> Hx.
set c := 5%:R^-1 - `|eps|.
have c0 : 0 < c by exact: eps_small.
have qimp : forall v, kim_qbar A v = 0 -> kim_q A x v = 0.
  move=> v /eqP; rewrite /kim_qbar mulf_eq0 invr_eq0 pnatr_eq0 /=.
  move=> /eqP Hsum0.
  have Hnn : forall i : bool * bool, ~~ (i.1 && i.2) -> 0 <= kim_q A i v
    by move=> i _; exact: kim_q_ge0.
  exact: (psumr_eq0P Hnn Hsum0 Hx).
apply: (order.Order.POrderTheory.le_trans
  (y := \sum_v (kim_q A x v - kim_qbar A v) ^+ 2 / c)).
  apply: ler_sum => v _.
  have [qv0 | qvN0] := eqVneq (kim_qbar A v) 0.
    by rewrite qv0 (qimp v qv0) subrr expr0n /= mul0r mul0r.
  apply: ler_wpM2l; first exact: sqr_ge0.
  have qpos : 0 < kim_qbar A v by rewrite lt0r qvN0 kim_qbar_ge0.
  rewrite lef_pV2 ?inE ?posrE //.
  by apply: kim_qbar_ge.
rewrite -mulr_suml.
apply: ler_wpM2r; first by rewrite invr_ge0 (order.Order.POrderTheory.ltW c0).
apply: (order.Order.POrderTheory.le_trans
  (y := (\sum_v `|kim_q A x v - kim_qbar A v|) ^+ 2)).
  rewrite expr2 big_distrl /=.
  apply: ler_sum => v _.
  rewrite -(@real_normK _ (kim_q A x v - kim_qbar A v)) ?num_real // expr2.
  apply: ler_wpM2l; first exact: normr_ge0.
  rewrite (bigD1 v) //= lerDl.
  by apply: sumr_ge0 => w _; exact: normr_ge0.
have Hd := kim_qbar_diff A Hx.
have Hs0 : 0 <= \sum_v `|kim_q A x v - kim_qbar A v|
  by apply: sumr_ge0 => v _; exact: normr_ge0.
apply: (order.Order.POrderTheory.le_trans (y := (4%:R * `|eps|) ^+ 2)).
  rewrite expr2 expr2.
  by apply: ler_pM; [exact: Hs0 | exact: Hs0 | exact: Hd | exact: Hd].
by rewrite exprMn -natrX /= real_normK ?num_real //.
Qed.

(** kim_div_bound — a false-fibre input's view law has KL against the mixed
    reference at most 16 eps^2 log e / (1/5 - |eps|).
    @composes: kim_input_private *)
Fact kim_div_bound (A : seq nat) (x : bool * bool) :
  ~~ (x.1 && x.2) ->
  \sum_v kim_q A x v * log (kim_q A x v / kim_qbar A v)
    <= 16%:R * eps ^+ 2 * log (sequences.expR 1) / (5%:R^-1 - `|eps|).
Proof.
move=> Hx.
have f0 : forall v, 0 <= [ffun v => kim_q A x v] v
  by move=> v; rewrite ffunE; exact: kim_q_ge0.
have f1 : \sum_w [ffun v => kim_q A x v] w = 1.
  by under eq_bigr do rewrite ffunE; exact: kim_qsum1.
pose P := FDist.make f0 f1.
have g0 : forall v, 0 <= [ffun v => kim_qbar A v] v
  by move=> v; rewrite ffunE; exact: kim_qbar_ge0.
have g1 : \sum_w [ffun v => kim_qbar A v] w = 1.
  by under eq_bigr do rewrite ffunE; exact: kim_qbar_sum1.
pose Q := FDist.make g0 g1.
have PvE : forall v, P v = kim_q A x v by move=> v; rewrite /P/= ffunE.
have QvE : forall v, Q v = kim_qbar A v by move=> v; rewrite /Q/= ffunE.
have qimp : forall v, kim_qbar A v = 0 -> kim_q A x v = 0.
  move=> v /eqP; rewrite /kim_qbar mulf_eq0 invr_eq0 pnatr_eq0 /=.
  move=> /eqP Hsum0.
  have Hnn : forall i : bool * bool, ~~ (i.1 && i.2) -> 0 <= kim_q A i v
    by move=> i _; exact: kim_q_ge0.
  exact: (psumr_eq0P Hnn Hsum0 Hx).
have key : divergence.div P Q <= chi2_div P Q * log (sequences.expR 1).
  apply: le_div_chi2; apply/dominatesP => v Qv0.
  by rewrite PvE; apply: qimp; rewrite -QvE.
have chi2le : chi2_div P Q <= 16%:R * eps ^+ 2 / (5%:R^-1 - `|eps|).
  rewrite /chi2_div; under eq_bigr => v _ do rewrite PvE QvE.
  exact: kim_chi2_bound.
rewrite (_ : \sum_v kim_q A x v * log (kim_q A x v / kim_qbar A v)
           = divergence.div P Q); last first.
  by rewrite /divergence.div; apply: eq_bigr => v _; rewrite PvE QvE.
apply: (order.Order.POrderTheory.le_trans key).
have RHSeq : 16%:R * eps ^+ 2 * log (sequences.expR 1) / (5%:R^-1 - `|eps|)
           = (16%:R * eps ^+ 2 / (5%:R^-1 - `|eps|)) * log (sequences.expR 1)
  by rewrite mulrAC.
rewrite RHSeq.
apply: ler_wpM2r; first exact: log_exp1_Rle_0.
exact: chi2le.
Qed.

(** kim_cdiv1_false — the output-false conditional KL term is the false-fibre
    average of the per-input view-law KL terms.
    @composes: kim_input_private *)
Fact kim_cdiv1_false (A : seq nat) :
  cdiv1 (PQR A) false =
  3%:R^-1 * \sum_(x in {: bool * bool} | ~~ (x.1 && x.2))
    \sum_v kim_q A x v * log (kim_q A x v / kim_qbar A v).
Proof.
have massE : forall (i : bool * bool) (v : (size A).-tuple bool) (s : bool),
    PQR A (i, v, s) = (i.1 && i.2 == s)%:R * (4%:R^-1 * kim_q A i v).
  move=> i v s.
  rewrite /PQR fdistmapE /=.
  rewrite (reindex (fun k : 'I_5 => ((i, k) : Omega))) /=; last first.
    exists (fun w : Omega => w.2) => [k _|w]; first by [].
    by case: w => [[a b] k] /=; rewrite inE /= => /eqP[] -> _ _.
  rewrite (eq_bigl
    (fun j : 'I_5 => (ViewA R A (i, j) == v) && (i.1 && i.2 == s))); last first.
    by move=> j; rewrite inE /=; case: i => i1 i2; rewrite !xpair_eqE !eqxx.
  have [Hs|Hs] := boolP (i.1 && i.2 == s).
    under eq_bigl => j do rewrite andbT.
    rewrite mul1r /kim_q mulr_sumr.
    by apply: eq_bigr => j _; rewrite kim_mass /=.
  by under eq_bigl => j do rewrite andbF; rewrite big_pred0_eq mul0r.
have D2E : (PQR A)`2 false = 3%:R / 4%:R.
  rewrite fdist_sndE.
  rewrite (eq_bigr (fun p : (bool * bool) * ((size A).-tuple bool) =>
    (p.1.1 && p.1.2 == false)%:R * (4%:R^-1 * kim_q A p.1 p.2))); last first.
    by move=> p _; rewrite -massE; case: p.
  rewrite -(pair_bigA _ (fun i v =>
    (i.1 && i.2 == false)%:R * (4%:R^-1 * kim_q A i v))) /=.
  under eq_bigr => i _ do rewrite -mulr_sumr -mulr_sumr kim_qsum1 mulr1.
  rewrite -mulr_suml.
  have S3 : \sum_(i : bool * bool) ((i.1 && i.2 == false)%:R) = 3%:R :> R.
    rewrite (bigD1 (false, false)) //= (bigD1 (false, true)) //=
      (bigD1 (true, false)) //=.
    by rewrite big1; [rewrite /= addr0; lra | move=> [[|] [|]]].
  by rewrite S3.
have jcE : forall (i : bool * bool) (v : (size A).-tuple bool),
    jfdist_cond.jcPr (PQR A) [set (i, v)] [set false]
      = (i.1 && i.2 == false)%:R * (3%:R^-1 * kim_q A i v).
  move=> i v.
  rewrite /jfdist_cond.jcPr ssr_ext.setX1 Pr_set1 Pr_set1 massE D2E.
  set c := (i.1 && i.2 == false)%:R; set q := kim_q A i v; lra.
have p13E : forall i : bool * bool,
    jfdist_cond.jcPr (fdist_proj13 (PQR A)) [set i] [set false]
      = (i.1 && i.2 == false)%:R * 3%:R^-1.
  move=> i.
  rewrite /jfdist_cond.jcPr ssr_ext.setX1 Pr_set1 Pr_set1.
  rewrite fdist_proj13_snd D2E fdist_proj13E /=.
  under eq_bigr => v _ do rewrite massE.
  rewrite -mulr_sumr -mulr_sumr kim_qsum1 mulr1.
  set c := (i.1 && i.2 == false)%:R; lra.
have p23E : forall v : (size A).-tuple bool,
    jfdist_cond.jcPr (fdist_proj23 (PQR A)) [set v] [set false] = kim_qbar A v.
  move=> v.
  rewrite /jfdist_cond.jcPr ssr_ext.setX1 Pr_set1 Pr_set1.
  rewrite fdist_proj23_snd D2E fdist_proj23E /=.
  under eq_bigr => i _ do rewrite massE mulr_natl mulrb.
  rewrite -big_mkcond /= -mulr_sumr.
  rewrite (eq_bigl (fun i : bool * bool => ~~ (i.1 && i.2))); last first.
    by move=> i; case: (i.1 && i.2).
  rewrite /kim_qbar.
  set S := \sum_(x in {: bool * bool} | ~~ (x.1 && x.2)) kim_q A x v; lra.
have jcE' : forall x : (bool * bool) * ((size A).-tuple bool),
    jfdist_cond.jcPr (PQR A) [set x] [set false]
      = (x.1.1 && x.1.2 == false)%:R * (3%:R^-1 * kim_q A x.1 x.2).
  by move=> [i v]; exact: jcE.
have ae : forall q qb : R, 3%:R^-1 * q / (3%:R^-1 * qb) = q / qb.
  move=> q qb; rewrite invfM invrK mulrACA mulVf ?mul1r//.
  by rewrite pnatr_eq0.
rewrite /cdiv1.
under eq_bigr => x _ do rewrite jcE' p13E p23E.
have term : forall (b : bool) (q qb : R),
    (b%:R * (3%:R^-1 * q)) * log (b%:R * (3%:R^-1 * q) / (b%:R / 3%:R * qb))
      = b%:R * (3%:R^-1 * (q * log (q / qb))).
  move=> [|] q qb; last by rewrite !mul0r.
  by rewrite !mul1r ae -mulrA.
under eq_bigr => x _ do rewrite term mulrCA.
rewrite -mulr_sumr.
under eq_bigr => x _ do rewrite mulr_natl mulrb.
rewrite -big_mkcond /=.
congr (_ * _).
rewrite (eq_bigl (fun i => (i.1.1 && i.1.2 == false) && true)); last first.
  by move=> i; rewrite andbT.
rewrite -(pair_big (fun a : bool * bool => a.1 && a.2 == false) xpredT
  (fun a v => kim_q A a v * log (kim_q A a v / kim_qbar A v))) /=.
apply: eq_bigl => i; by case: (i.1 && i.2).
Qed.

(** kim_input_private — under Kim's biased cut, a partial view carries at most
    kim_leak_bound eps conditional mutual information about the inputs given the
    output a && b.
    @main security: cond_mutual_info bound on inputs vs view given the secret. *)
Lemma kim_input_private (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps.
Proof.
rewrite -/(PQR A) kim_cond_mutual_infoE kim_cdiv1_false.
set D := 5%:R^-1 - `|eps|.
pose C := 16%:R * eps ^+ 2 * log (sequences.expR 1) / D.
apply: (order.Order.POrderTheory.le_trans
  (y := 3%:R / 4%:R * (3%:R^-1 * \sum_(x in {: bool * bool} | ~~ (x.1 && x.2)) C))).
  apply: ler_wpM2l; first by apply: divr_ge0; apply: ler0n.
  apply: ler_wpM2l; first by rewrite invr_ge0 ler0n.
  by apply: ler_sum => x Hx; exact: kim_div_bound.
rewrite sumr_const.
have Hc3 : #|(fun i : bool * bool => ~~ (i.1 && i.2))| = 3%N.
  rewrite -sum1_card.
  rewrite (bigD1 (false, false)) //= (bigD1 (false, true)) //=
    (bigD1 (true, false)) //=.
  by rewrite big1 ?addn0; [ | by move=> [[|] [|]]].
rewrite Hc3.
have e1 : C = 16%:R * (eps ^+ 2 * log (sequences.expR 1) / D)
  by rewrite /C -!mulrA.
have e2 : kim_leak_bound eps = 12%:R * (eps ^+ 2 * log (sequences.expR 1) / D)
  by rewrite /kim_leak_bound -/D [eps ^+ 2 * _]mulrC -!mulrA.
rewrite e1 e2.
set w := eps ^+ 2 * log (sequences.expR 1) / D.
by lra.
Qed.

End kim_input_privacy.

(** kim_input_private0 — at zero bias the conditional mutual information meets
    kim_leak_bound 0, the unbiased (den Boer) endpoint of the O(eps^2) ceiling.
    @composes: kim_input_private *)
Corollary kim_input_private0 (R : realType)
    (H1 : (0 : R) < 5%:R^-1) (H2 : - (4%:R * 5%:R^-1) < (0 : R))
    (H3 : 0 < 5%:R^-1 - `|0 : R|) (A : seq nat) :
  cond_mutual_info
    (`p_ [% @kim_inputs R 0 H1 H2, @kim_view R 0 H1 H2 A, @kim_secret R 0 H1 H2])
    <= @kim_leak_bound R 0.
Proof. exact: (@kim_input_private R 0 H1 H2 H3 A). Qed.
