(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* PGG: quantitative SecurityWitness for Z_7 wr S_2                           *)
(*                                                                            *)
(* At word length L = 1 the achievable shuffles are exactly the three         *)
(* generators {cut1, cut2, wswap}, and they send every card to three          *)
(* distinct positions: a cut fixes the other pile, the swap crosses piles.    *)
(* So sigma |-> sigma s is injective on the achievable set, and the direct    *)
(* endpoint constructor security_witness_endpoint_inj gives a fully proven    *)
(* bound epsilon = 2 * (14 - 3) / 14 = 11/7, with no admitted var_dist        *)
(* computation. This is the quantitative security knob; the structural        *)
(* anonymity is |G| = 98 (see pgg_wreath.card_wreath, rigidity_wreath).       *)
(******************************************************************************)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import div fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism action bigop order ssrnum.
From mathcomp Require Import boolp reals.
From infotheo Require Import realType_ext fdist proba variation_dist.
Require Import pgg_interface.
From pgg_smc Require Import pgg_weval_inj pgg_wreath.
From pgg_reconstruct Require Import pgg_sharing_framework covering_scheme
                                    cover_tradeoff algebraic_rigidity.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section wreath_security.

Variable R : realType.

(** wreath_perm_endpoint_inj1 — the three achievable shuffles separate every card.
    Kind: main.
    Why: at L = 1 the achievable set is {cut1, cut2, wswap}; for each start card s,
    sigma |-> sigma s is injective on it (a cut fixes the other pile, the swap
    crosses piles, so the three images are distinct). Feeds the direct endpoint
    SecurityWitness constructor.
    Used by: wreath_security_witness. *)
Lemma wreath_perm_endpoint_inj1 :
  forall s : 'I_14,
  {in @achievable M_wreath 1 &,
   injective (fun sigma : {perm 'I_14} => sigma s)}.
Proof.
move=> s x y Hx Hy Hf; move: Hf.
rewrite /achievable in Hx Hy.
case/imsetP: Hx => wx _ ->.
case/imsetP: Hy => wy _ ->.
rewrite /word_eval !big_ord_recr !big_ord0 /= !mul1g => Hf.
move: (tnth wx ord_max) (tnth wy ord_max) Hf => i j.
rewrite /pgg_sigmas !(tnth_nth 1%g) /=.
case: i => [[|[|[|i]]] Hi] //; case: j => [[|[|[|j]]] Hj] //=;
  case: s => [[|[|[|[|[|[|[|[|[|[|[|[|[|[|s]]]]]]]]]]]]]] Hs] //= => Hf;
  by have := congr1 val Hf; rewrite ?permM ?permE /=.
Qed.

(** wreath_security_witness — the quantitative SecurityWitness at L = 1.
    Kind: instance.
    Why: the security artifact of the wreath instance; epsilon = 2*(14-3)/14
    derived by the direct endpoint constructor from word-eval injectivity and the
    endpoint-injectivity above. No admitted var_dist bound. *)
Definition wreath_security_witness : SecurityWitness R M_wreath :=
  security_witness_endpoint_inj R wreath_weval_inj1 wreath_perm_endpoint_inj1.

End wreath_security.
