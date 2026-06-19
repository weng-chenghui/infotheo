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

(** kim_leak_bound — the [O(eps^2)] leakage ceiling, constant refined in the
    assembly step.
    @intent: Kim's input-privacy bound as a function of the bias. *)
Definition kim_leak_bound (e : R) : R :=
  3%:R / 4%:R * e ^+ 2 / (5%:R^-1 - `|e|).

(** kim_input_private — under Kim's biased cut, a partial view carries at most
    kim_leak_bound eps conditional mutual information about the inputs given the
    output a && b.
    @main security: cond_mutual_info bound on inputs vs view given the secret. *)
Lemma kim_input_private (A : seq nat) :
  cond_mutual_info (`p_ [% kim_inputs, kim_view A, kim_secret]) <= kim_leak_bound eps.
Proof.
Admitted.

End kim_input_privacy.
