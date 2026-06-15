(* FEASIBILITY PROBE (throwaway) for option B.  Mirrors the fiber file preamble
   so the SSProve types (uniform, cells, Pr_fst) resolve, then tests the three
   uncertain reflection mechanics on a toy with the real experiment shape:
     x  <- sample uniform card ;;       (* the V2 sample *)
     #put cell := Some x ;;             (* run writes the cell *)
     v  <- get cell ;;                  (* challenger reads it BEFORE the predictor *)
     g  <- pred ;;                      (* opaque, closed, lossless guesser *)
     ret (g, v)
   Goals:
   (P1) reflect Pr_fst toy to an explicit dlet over the uniform sample (get-after-
        put returns the sampled x; opaque pred kept abstract via Pr_fst_bind);
   (P2) the diagonal collision sum is <= 1/card. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra fingroup finalg.
From mathcomp Require Import matrix ring boolp finmap reals realsum.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package pkg_composition Pr.
From SSProve.Crypt Require Import HybridArgument.
Set Warnings "notation-overridden,ambiguous-paths".

From Stdlib Require Import Utf8.
From extructures Require Import ord fset fmap.

Require Import realType_ext.

Set Implicit Arguments.
Unset Strict Implicit.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Notation R := SSProve.Crypt.Axioms.R.

Section probe.

(* a choice carrier for the sampled value and the cell, mirroring t_msg. *)
Variable card : nat.
Hypothesis Hcard : (0 < card)%N.
Let T : choice_type := 'fin card.
Let cell : Location := mkloc 0 (None : option T).

(* the opaque closed guesser: imports nothing, returns a T. *)
Variable pred : raw_code T.
Hypothesis Hpred_valid : ValidCode emptym [interface] pred.
Hypothesis Hpred_ll : psum (distr.mu (Pr_fst pred)) = (1 : R).

(* toy experiment: sample, put, read-before-pred, opaque guess, return pair. *)
Definition toy : raw_code (T × T)%type :=
  x ← sample uniform card ;;
  #put cell := Some x ;;
  ov ← get cell ;;
  g ← pred ;;
  ret (g, odflt x ov).

(* CRUX PROBE: the footprint lemma.  A closed predictor (no locations, no
   imports) has a heap-INDEPENDENT value-marginal: dfst (Pr_code c h) = Pr_fst c
   for every h.  This is what stops the predictor from reading V_2_cell.
   Proved by induction on c + inversion of validity: opr/getr/putr vacuous. *)
Lemma Pr_fst_closed {A : choice_type} (c : raw_code A) :
  ValidCode emptym [interface] c ->
  forall h, distr.dmargin fst (Pr_code c h) = Pr_fst c.
Proof.
induction 1 as [x | o x k Hin IH | l k Hin IH | l v Hin IH | op k IH]; intros h.
- apply: SubDistr.distr_ext => w; rewrite Pr_code_ret /Pr_fst Pr_code_ret 2!distr.dmargin_dunit //.
- exfalso; eapply fhas_empty; eassumption.
- exfalso; eapply fhas_empty; eassumption.
- exfalso; eapply fhas_empty; eassumption.
rewrite Pr_code_sample Pr_fst_sample distr.dmarginE dlet_dlet_ext.
apply: eq_dlet => y.
rewrite -distr.dmarginE.
exact: H.
Qed.

(* INTEGRATION PROBE: reflect the concrete game (sample;;put;;get) AND eliminate
   the opaque predictor's heap-dependence via the footprint lemma, giving the
   explicit pushforward.  This is the exact pattern the real denote_run needs. *)
Lemma toy_reflect :
  Pr_fst toy
  = distr.dlet
      (fun x => distr.dlet (fun g => distr.dunit (g, x)) (Pr_fst pred))
      (projT2 (uniform card)).
Proof.
Admitted.

(* P2: the diagonal collision probability is at most 1/card. *)
Lemma toy_bound :
  psum (fun gv : (T × T)%type => (gv.1 == gv.2)%:R * distr.mu (Pr_fst toy) gv)
    <= card%:R^-1.
Proof.
Admitted.

End probe.
