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
  have [N fN] := fn c; near=> n; apply: fN.
  by near: n; exact: nbhs_infty_gt.
by have [N _ fN] := fn c; exists N => n Nn; apply: fN; exact: ltnW.
Unshelve. all: by end_near. Qed.

(* A nonnegative f is negligible iff n ^+ c * f n tends to 0 along \oo at
   every exponent c.  Negligibility is the convergence to 0 of f against
   every polynomial weight. *)
Lemma negligible_fun_cvgP f : (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c : nat, (fun n => n%:R ^+ c * f n) @ \oo --> 0.
Proof.
move=> f_ge0; split=> [/negligible_fun_nearP fn c|fn].
  apply/cvgr0Pnorm_lt => e e_gt0; near=> n.
  have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
  rewrite normrM normrX normr_nat ger0_norm ?f_ge0//.
  have : f n < n%:R ^- c.+1 by near: n; exact: fn.
  rewrite -(ltr_pM2l (_ : 0 < n%:R ^+ c)) ?exprn_gt0 ?ltr0n // exprSr invfM.
  rewrite mulVKf ?expf_neq0 ?pnatr_eq0 -?lt0n // => /lt_trans; apply.
  rewrite -[e]invrK ltf_pV2 ?posrE ?ltr0n ?invr_gt0 //.
  by near: n; exact: nbhs_infty_gtr.
apply/negligible_fun_nearP => c; near=> n.
have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
have : `|n%:R ^+ c * f n| < 1.
  by near: n; apply: (cvgr0Pnorm_lt _).1 ltr01; exact: fn.
rewrite normrM normrX normr_nat ger0_norm ?f_ge0//.
by rewrite -ltr_pdivlMl ?exprn_gt0 ?ltr0n ?mulr1.
Unshelve. all: by end_near. Qed.

(* A nonnegative f is negligible iff f is little-o of n ^- c along \oo at
   every exponent c.  This is the Landau reading f = o(n ^- c) at every
   order c. *)
Lemma negligible_fun_eqoP f : (forall n, 0 <= f n) ->
  negligible_fun f <-> forall c : nat, f =o_\oo (fun n => n%:R ^- c : R).
Proof.
move=> f_ge0; split=> [/(negligible_fun_cvgP f_ge0) fn c|fo].
  apply/eqoP => e e_gt0; near=> n.
  have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
  have : `|n%:R ^+ c * f n| < e.
    by near: n; apply: (cvgr0Pnorm_lt _).1 e_gt0; exact: fn.
  rewrite normrM normrX normr_nat normfV normrX normr_nat.
  by rewrite ler_pdivlMr ?exprn_gt0 ?ltr0n // mulrC => /ltW.
apply/negligible_fun_nearP => c; near=> n.
have n_gt0 : (0 < n)%N by near: n; exact: nbhs_infty_gt.
have : `|f n| <= 2^-1 * `|n%:R ^- c : R|.
  by near: n; apply: (eqoP _ _ _).1 (fo c) _ _; rewrite invr_gt0 ltr0n.
rewrite ger0_norm ?f_ge0// normfV normrX normr_nat => /le_lt_trans; apply.
by rewrite gtr_pMl ?invf_lt1 ?ltr1n // invr_gt0 exprn_gt0 ?ltr0n.
Unshelve. all: by end_near. Qed.

End negligible_littleo.
