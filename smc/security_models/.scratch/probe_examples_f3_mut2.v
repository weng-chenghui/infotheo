(* MUTATION COPY 2 of probe_examples_f3.v — expected to FAIL.
   mask_chan_uniform_hides is restated with biased3 in place of unif3;
   nothing else changes.  The mutated statement is refuted by
   mask_chan_biased_leaks at x = 0, x' = 1.                          *)

(* Probe D4+D2 — the 'F_3 example layer of examples_f3.v and the log API
   smoke test for unpredictability.v.
   Claims under test:
   D4a  fdist_uniform at 'F_3; mask channel via fdistmap; uniform mask
        hides the input (columns equal, ex:smc:mask-matrix).
   D4b  a concrete biased law (1/2, 1/4, 1/4) on 'F_3 is constructible
        (fdist_convn over 'I_3, or any stock constructor); its mask
        channel leaks (two columns differ, ex:smc:mask-matrix).
   D4c  statdist (biased column) (uniform column) computes to 6^-1 —
        the epsilon of the approximate verdict (tab:smc:privacy-laws).
   D4d  dirac (+1) evaluates as the permutation matrix
        (ex:smc:dirac-matrix) and fdistmap add (draw x) = mask_chan x
        (ex:smc:ancilla-matrix).
   D2   realType_ln's logarithm: name, base, monotonicity lemma usable
        for H_unp >= -log(...) style bounds.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_examples_f3.v              *)

(* FINDINGS
   1. Cardinality argument.  'F_3 is 'I_3 up to conversion, so the
      argument fdist_uniform expects is discharged by card_ord; the
      probe adds the local card_F3 : #|F3| = 3 and takes
      unif3 := fdist_uniform card_F3.  card_Fp is not needed.
   2. Constructor for biased3.  The stock binary convex combination
      fdist_conv, notation p <| _ |> q (probability/fdist.v:880-894),
      nested twice over fdist1: biased3 puts 1/2 on 0 and splits the
      remaining half evenly over 1 and 1+1.  The weight literal is
      (2^-1 : R)%:pr : {prob R}; realType_ext's %:pr (line 225) fills
      the 0 <= 2^-1 <= 1 side condition from the {i01 R} canonical
      instances, so no auxiliary proof is written.  fdist_convn over
      'I_3 was rejected: it takes a weight fdist on 'I_3, which is the
      same construction problem one level down.
   3. Pointwise evaluation of biased3 is fdist_convE + fdist1E + /=:
      equality of 'F_3 literals (for instance 1 + 1 == 1) reduces by
      computation, so the indicator terms disappear on their own and
      only onemE + lra remain.
   4. Enumerating a sum over F3: big_ord_recl applies even though the
      index is the FinRing join instance of 'I_3.  ord0 is 0 by
      conversion; the other two points are named by val_inj.
   5. `x is the binary product fdist_prod P (fun=> Q) (fdist.v:1071),
      so tensor needed no adaptation.  draw_add_mask factors through
      tensor_dirac_l : tensor (fdist1 x) m = fdistmap (pair x) m, after
      which fdistmap_comp closes it, the composite being convertible
      to the masking map.
   6. D4c is TRUE as stated: |1/2 - 1/3| + 2 * |1/4 - 1/3| =
      1/6 + 2 * (1/12) = 1/3, and half of that is 6^-1.
   7. Logarithm identifiers.  The base-2 logarithm is log
      (lib/realType_ln.v:177), defined as Log 2 with
      Log n x = ln x / ln n.-1.+1%:R (line 86).  Its monotonicity is
      ler_log (line 185), stated as an in-domain monotonicity
      {in Num.pos &, {mono log : x y / x <= y}} rather than a bare
      implication, so the probe keeps its own statement shape and
      derives it; Log_increasing_le (line 108) is the deprecated
      implication form at Log n.  No spelling change was needed: log
      is the literal identifier.                                     *)

From mathcomp Require Import all_ssreflect all_algebra finalg reals lra.
Require Import realType_ext realType_ln fdist proba.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section f3_examples.
Context {R : realType}.
Let F3 : finType := 'F_3.

(* D4a: uniform law on 'F_3 (FINDING 1). *)
Lemma card_F3 : #|F3| = 3.
Proof. by rewrite card_ord. Qed.

Definition unif3 : R.-fdist F3 := fdist_uniform card_F3.

Definition mask_chan (m : R.-fdist F3) (x : F3) : R.-fdist F3 :=
  fdistmap (fun s => x + s) m.

(* The mask channel reads off the mask law at the shifted point. *)
Lemma mask_chanE (m : R.-fdist F3) (x b : F3) :
  mask_chan m x b = m (- x + b).
Proof.
rewrite /mask_chan fdistmapE (big_pred1 (- x + b)) //.
by move=> a; rewrite /= !inE (can2_eq (addKr x) (addNKr x)).
Qed.

(* The mutated lemma sits below, after biased3 is in scope. *)

(* D4b: the biased mask (1/2, 1/4, 1/4) (FINDING 2). *)
Definition biased3 : R.-fdist F3 :=
  (fdist1 0 <| (2^-1 : R)%:pr |>
     (fdist1 1 <| (2^-1 : R)%:pr |> fdist1 (1 + 1)))%fdist.

Lemma biased3_0 : biased3 0 = 2^-1.
Proof.
rewrite /biased3 !fdist_convE !fdist1E /=.
by rewrite mulr0 mulr0 addr0 mulr0 addr0 mulr1.
Qed.

Lemma biased3_1 : biased3 1 = 4^-1.
Proof. by rewrite /biased3 !fdist_convE !fdist1E /= onemE; lra. Qed.

Lemma biased3_2 : biased3 (1 + 1) = 4^-1.
Proof. by rewrite /biased3 !fdist_convE !fdist1E /= onemE; lra. Qed.

Lemma mask_chan_uniform_hides (x x' : F3) :
  mask_chan biased3 x = mask_chan biased3 x'.
Proof.
by apply/fdist_ext => b; rewrite !mask_chanE /unif3 !fdist_uniformE.
Qed.

Lemma mask_chan_biased_leaks :
  mask_chan biased3 0 <> mask_chan biased3 1.
Proof.
move=> /(congr1 (fun d : R.-fdist F3 => d 1)) /=.
by rewrite !mask_chanE oppr0 add0r addNr biased3_0 biased3_1; lra.
Qed.

(* D4c: the epsilon of the approximate verdict.  statdist as in probe
   P2 (duplicate the definition locally; .scratch is not importable). *)
Definition statdist (p q : R.-fdist F3) : R :=
  2%:R^-1 * \sum_b `|p b - q b|.

Lemma biased_uniform_eps : statdist biased3 unif3 = 6%:R^-1.
Proof.
rewrite /statdist /unif3.
under eq_bigr do rewrite fdist_uniformE card_F3.
rewrite !big_ord_recl big_ord0.
rewrite (_ : lift ord0 (lift ord0 ord0) = 1 + 1 :> F3); last exact/val_inj.
rewrite (_ : lift ord0 ord0 = 1 :> F3); last exact/val_inj.
rewrite biased3_0 biased3_1 biased3_2.
by rewrite ger0_norm ?ler0_norm; lra.
Qed.

(* D4d: Dirac shift as the permutation matrix; ancilla-draw compose. *)
Lemma dirac_shiftE (x y : F3) :
  fdist1 (x + 1) y = (y == x + 1)%:R :> R.
Proof. by rewrite fdist1E eq_sym. Qed.

Definition tensor (p : R.-fdist F3) (q : R.-fdist F3)
  : R.-fdist (F3 * F3)%type := (p `x q)%fdist.

(* A Dirac left factor turns the product into a pairing map. *)
Lemma tensor_dirac_l (m : R.-fdist F3) (x : F3) :
  tensor (fdist1 x) m = fdistmap (fun s => (x, s)) m.
Proof.
apply/fdist_ext => -[a b]; rewrite /tensor fdist_prodE fdist1E fdistmapE /=.
case: (eqVneq a x) => [->|ax].
  rewrite mul1r (big_pred1 b) //.
  by move=> a0; rewrite /= !inE xpair_eqE eqxx.
rewrite mul0r big_pred0 // => a0.
by rewrite /= !inE xpair_eqE eq_sym (negbTE ax).
Qed.

Lemma draw_add_mask (m : R.-fdist F3) (x : F3) :
  fdistmap (fun e : F3 * F3 => e.1 + e.2) (tensor (fdist1 x) m)
  = mask_chan m x.
Proof. by rewrite tensor_dirac_l fdistmap_comp. Qed.

End f3_examples.

Section log_api.
Context {R : realType}.
(* D2: the base-2 log of realType_ln (FINDING 7). *)
Lemma log_le_probe (a b : R) : 0 < a -> a <= b -> log a <= log b.
Proof.
move=> a0 ab; rewrite ler_log ?posrE//.
exact: lt_le_trans a0 ab.
Qed.

Lemma log_neg_probe (a b : R) : 0 < a -> a <= b -> - log b <= - log a.
Proof. by move=> a0 ab; rewrite lerN2 log_le_probe. Qed.
End log_api.

Print Assumptions biased_uniform_eps.
Print Assumptions draw_add_mask.
Print Assumptions log_neg_probe.

(* MUTATION CHECKS — both copies live in this directory and both fail.
   1. probe_examples_f3_mut1.v : biased_uniform_eps with RHS 4%:R^-1.
      Error at the closing lra of biased_uniform_eps:
        Tactic failure: Cannot find witness.
   2. probe_examples_f3_mut2.v : mask_chan_uniform_hides restated with
      biased3 in place of unif3.
      Error at the rewrite of mask_chan_uniform_hides:
        The LHS of fdist_uniformE (fdist_uniform _ _) does not match
        any subterm of the goal.                                     *)
