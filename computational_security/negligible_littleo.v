From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import classical_sets reals topology normedtype landau.
Require Import negligible.

(**md**************************************************************************)
(* # Negligibility in the vocabulary of filters and little-o                  *)
(*                                                                            *)
(* The security bounds of the project hold one instance per security          *)
(* parameter k, and negligible_fun reads such a sequence asymptotically: f    *)
(* eventually falls below every inverse monomial n ^- c.  This file states    *)
(* that reading in the vocabulary of mathcomp-analysis: an eventual bound     *)
(* along the filter \oo of nat, the convergence of n ^+ c * f n to 0 along    *)
(* \oo, and f =o_\oo n ^- c.  Results of analysis on filters, limits and      *)
(* Landau notation then apply to negligible functions.                        *)
(*                                                                            *)
(* The eventual form holds for every f.  The convergence and little-o forms   *)
(* assume f nonnegative: negligible_fun bounds f n from above only, a bound   *)
(* that every negative constant meets, while both analysis forms bound |f n|. *)
(*                                                                            *)
(* ```                                                                        *)
(* negligible_fun_nearP == negligible_fun f iff f n < n ^- c holds near \oo   *)
(*                         for every exponent c                               *)
(*  negligible_fun_cvgP == a nonnegative f is negligible iff n ^+ c * f n     *)
(*                         tends to 0 along \oo for every exponent c          *)
(*  negligible_fun_eqoP == a nonnegative f is negligible iff f =o_\oo n ^- c  *)
(*                         for every exponent c                               *)
(* ```                                                                        *)
(*                                                                            *)
(******************************************************************************)

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

Section negligible_littleo.
Context {R : realType}.
Implicit Types f : nat -> R.

(* negligible_fun f is the bound f n < n ^- c eventually along the filter \oo
   of nat, at every exponent c.  Filter lemmas of analysis thereby become
   lemmas on negligible functions. *)
Lemma negligible_fun_nearP f :
  negligible_fun f <-> forall c : nat, \forall n \near \oo, f n < n%:R ^- c.
Proof.
split=> [fn c|fn c].
  by have [N fN] := fn c; exact: filterS fN (nbhs_infty_gt N).
by have [N _ fN] := fn c; exists N => n Nn; apply: fN; exact: ltnW.
Qed.

(* A nonnegative f is negligible iff n ^+ c * f n tends to 0 along \oo at
   every exponent c.  Negligibility is the convergence to 0 of f against
   every polynomial weight. *)
Lemma negligible_fun_cvgP f : (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c : nat, (fun n => n%:R ^+ c * f n) @ \oo --> 0.
Proof.
move=> f_ge0; split=> [/negligible_fun_nearP fn c|fn].
  apply/cvgr0Pnorm_lt => e e_gt0; near=> n.
  have n_gt0 : 0 < n%:R :> R by near: n; exact: nbhs_infty_gtr.
  rewrite ger0_norm ?mulr_ge0 ?exprn_ge0 ?f_ge0// -ltr_pdivlMl ?exprn_gt0//.
  apply: (@lt_trans _ _ (n%:R ^- c.+1)); first by near: n; exact: fn.
  rewrite exprSr invfM ltr_pM2l ?invr_gt0 ?exprn_gt0// invf_plt//.
  by near: n; exact: nbhs_infty_gtr.
apply/negligible_fun_nearP => c; near=> n.
have n_gt0 : 0 < n%:R :> R by near: n; exact: nbhs_infty_gtr.
rewrite -[_ ^- c]mulr1 ltr_pdivlMl ?exprn_gt0//.
apply: le_lt_trans (ler_norm _) _.
by near: n; apply: (cvgr0Pnorm_lt _).1 ltr01; exact: fn.
Unshelve. all: by end_near. Qed.

(* A nonnegative f is negligible iff f is little-o of n ^- c along \oo at
   every exponent c.  This is the Landau reading f = o(n ^- c) at every
   order c. *)
Lemma negligible_fun_eqoP f : (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c : nat, f =o_\oo (fun n => n%:R ^- c : R).
Proof.
move=> f_ge0; split=> [/(negligible_fun_cvgP f_ge0) fn c|fo].
  apply/eqoP => e e_gt0; near=> n.
  have n_gt0 : 0 < n%:R :> R by near: n; exact: nbhs_infty_gtr.
  rewrite normfV ler_pdivlMr ?normr_gt0 ?expf_neq0 ?gt_eqF// mulrC -normrM.
  by apply/ltW; near: n; apply: (cvgr0Pnorm_lt _).1 e_gt0; exact: fn.
apply/negligible_fun_nearP => c; near=> n.
have n_gt0 : 0 < n%:R :> R by near: n; exact: nbhs_infty_gtr.
apply: le_lt_trans (ler_norm _) (le_lt_trans (_ : _ <= 2^-1 * `|n%:R ^- c|) _).
  by near: n; apply: (eqoP _ _ _).1 (fo c) _ _; rewrite invr_gt0 ltr0n.
by rewrite gtr0_norm ?gtr_pMl ?invf_lt1 ?ltr1n ?invr_gt0 ?exprn_gt0.
Unshelve. all: by end_near. Qed.

End negligible_littleo.
