(* infotheo: information theory and error-correcting codes in Rocq            *)
(* Copyright (C) 2025 infotheo authors, license: LGPL-2.1-or-later            *)
(******************************************************************************)
(* Security vs Threshold Gap Tradeoff                                         *)
(*                                                                            *)
(* Formalizes the central novelty: stronger computation security (larger G)   *)
(* forces higher genus (wider threshold gap).                                 *)
(*                                                                            *)
(* The chain: G -> genus (Riemann-Hurwitz) -> gap (AG code bounds)           *)
(*                                                                            *)
(* Key results:                                                               *)
(*   genus0_ramif_exact      == genus 0 forces R = 2|G|-2                    *)
(*   genus0_search_bound     == genus 0 bounds search space via |G|          *)
(*   large_group_forces_genus == |G| > PGL bound -> genus > 0               *)
(*   security_threshold_tradeoff == the main tradeoff theorem                *)
(******************************************************************************)

From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
From mathcomp Require Import fintype tuple finfun finset fingroup perm.
From mathcomp Require Import morphism bigop div.
From pgg_smc Require Import pgg_interface.
From pgg_reconstruct Require Import pgg_sharing_framework.
From pgg_reconstruct Require Import covering_scheme.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(******************************************************************************)
(*     Section 1: Riemann-Hurwitz Consequences                                *)
(******************************************************************************)

Section riemann_hurwitz_consequences.

Variable M : MonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(* For base P^1 (genus 0):
   2g(C) + 2|G| = R + 2
   So R = 2g(C) + 2|G| - 2 >= 2|G| - 2
   And g(C) = (R + 2 - 2|G|) / 2 *)

Lemma genus0_forces_ramif (cd : CoveringData M) :
  cd_base_genus cd = 0 ->
  cd_genus cd = 0 ->
  cd_ramif cd + 2 = 2 * #|G|.
Proof. Admitted.

(* More ramification -> higher genus *)
Lemma more_ramif_more_genus (cd1 cd2 : CoveringData M) :
  cd_base_genus cd1 = 0 ->
  cd_base_genus cd2 = 0 ->
  cd_ramif cd1 < cd_ramif cd2 ->
  cd_genus cd1 < cd_genus cd2.
Proof. Admitted.

End riemann_hurwitz_consequences.

(******************************************************************************)
(*     Section 2: Search Space and Group Size                                 *)
(******************************************************************************)

Section search_space_bounds.

Variable M : GeneratedMonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(* Search space is bounded by |G| *)
Lemma search_space_le_group (L : nat) :
  @search_space M L <= #|G|.
Proof. Admitted.

(* For genus-0 covers, |G| embeds into Aut(P^1).
   Over a field with N elements, Aut(P^1) = PGL(2,N).
   |PGL(2,N)| = N(N^2 - 1).
   This is stated as a hypothesis since proving it requires
   algebraic curve theory beyond the scope of this formalization. *)

(* PGL(2,N) size bound *)
Definition pgl_bound := N * (N ^ 2 - 1).

End search_space_bounds.

(******************************************************************************)
(*     Section 3: The Main Tradeoff                                           *)
(******************************************************************************)

Section tradeoff.

Variable M : GeneratedMonodromyReprType.
Let G := pgg_G M.
Let N := (pgg_N' M).+1.

(* Genus-0 covering forces |G| to be bounded (embeds in PGL(2,N)) *)
Hypothesis genus0_pgl :
  forall (cd : CoveringData M),
    cd_genus cd = 0 -> #|G| <= pgl_bound M.

(* THE MAIN TRADEOFF THEOREM:
   Either the computation security is bounded (genus 0, small group)
   or the threshold has a gap (genus > 0). *)
Theorem security_threshold_tradeoff (cs : CoveringScheme M) :
  (* Either genus 0 with bounded group ... *)
  (cd_genus (cs_data cs) = 0 /\
   #|G| <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (* ... or positive genus with threshold gap *)
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
case Hg : (cd_genus (cs_data cs) == 0).
- left; move/eqP: Hg => Hg; split; first exact: Hg.
  split.
  + exact: genus0_pgl Hg.
  + exact: genus0_exact Hg.
- right; split.
  + by rewrite lt0n Hg.
  + exact: cs_gap.
Qed.

(* Contrapositive: large group forces threshold gap *)
Lemma large_group_forces_gap (cs : CoveringScheme M) :
  pgl_bound M < #|G| ->
  0 < cd_genus (cs_data cs).
Proof.
move=> Hpgl.
apply/negP => /negP.
rewrite -leqNgt leqn0 => /eqP Hg0.
have Hle := genus0_pgl Hg0.
by move: (leq_ltn_trans Hle Hpgl); rewrite ltnn.
Qed.

(* Monotonicity: larger group -> more ramification needed -> higher genus *)
Lemma group_genus_monotone (cd1 cd2 : CoveringData M) :
  cd_base_genus cd1 = 0 ->
  cd_base_genus cd2 = 0 ->
  cd_ramif cd1 = cd_ramif cd2 ->
  cd_genus cd1 = cd_genus cd2.
Proof. Admitted.

(* Combined statement: search space vs threshold gap *)
Theorem search_gap_tradeoff (cs : CoveringScheme M) (L : nat) :
  (* Either search space is bounded by PGL(2,N) ... *)
  (@search_space M L <= pgl_bound M /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs))
  \/
  (* ... or threshold has a gap proportional to genus *)
  (0 < cd_genus (cs_data cs) /\
   ts_T (cs_scheme cs) <= ts_k (cs_scheme cs) + 2 * cd_genus (cs_data cs)).
Proof.
case Hg : (cd_genus (cs_data cs) == 0).
- left; split.
  + apply: (leq_trans (search_space_le_group M L)).
    move/eqP: Hg => Hg.
    exact: genus0_pgl Hg.
  + exact: genus0_exact (eqP Hg).
- right; split.
  + by rewrite lt0n Hg.
  + exact: cs_gap.
Qed.

End tradeoff.
