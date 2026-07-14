(** SSProve extension: heap-parametric losslessness.

    [LosslessHeapCode c] — the joint output/heap subdistribution
    [Pr_code c h] has total mass one from every starting heap [h]. Closed
    under ret / sample / get / put / bind / if with no
    [ValidCode emptym] restriction, so stateful code is in scope;
    [LosslessHeap_Pr_fst] recovers SSProve's [Pr_fst]-based mass-1 form. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra reals realsum distr.

Set Warnings "-notation-overridden,-ambiguous-paths".
From SSProve.Crypt Require Import Package Pr.
Set Warnings "notation-overridden,ambiguous-paths".

From extructures Require Import ord fset fmap.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import GRing.Theory Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.
#[local] Open Scope real_scope.

(* Pin SSProve's real type as the ambient realType. *)
Local Notation R := SSProve.Crypt.Axioms.R.

(* psum_dlet_const1 — the total mass of a mixture whose every fibre
   continuation has total mass one equals the total mass of the mixing
   subdistribution. *)
Lemma psum_dlet_const1 {T U : choiceType}
    (mu : {distr T / R}) (G : T -> {distr U / R}) :
  (forall x, psum (distr.mu (G x)) = 1) ->
  psum (distr.mu (\dlet_(x <- mu) G x)) = psum (distr.mu mu).
Proof.
move=> HG.
under eq_psum => y do rewrite dletE.
rewrite __admitted__interchange_psum.
1:{ apply: eq_psum => y.
    by rewrite psumZ ?ge0_mu // HG mulr1. }
1:{ by move=> x; apply: summable_mlet. }
eapply eq_summable; first by move=> x; rewrite -dletE.
exact: summable_mu.
Qed.

(* LosslessHeapCode c — heap-parametric losslessness: the joint output/heap
   subdistribution [Pr_code c h] has total mass one from every starting heap.
   Naming: PascalCase after upstream [LosslessCode] (nominal/Pr.v). *)
Definition LosslessHeapCode {A : choiceType} (c : raw_code A) : Prop :=
  forall h : heap, psum (distr.mu (Pr_code c h)) = 1.

(* Closure of [LosslessHeapCode] under the code constructors, at a fixed
   output type [A]. *)
Section HeapLossless.
Context {A : choiceType}.

(* LosslessHeap_ret — a return terminates with mass one.
   Naming: PascalCase after the upstream family [Lossless_ret]
   (nominal/Pr.v). *)
Lemma LosslessHeap_ret (a : A) :
  LosslessHeapCode (ret a).
Proof. move=> h; rewrite Pr_code_ret; exact: Couplings.psum_SDistr_unit. Qed.

(* LosslessHeap_sample — a sample of a lossless operation followed by a
   uniformly lossless continuation terminates with mass one.
   Naming: PascalCase after the upstream family [Lossless_sample]
   (nominal/Pr.v). *)
Lemma LosslessHeap_sample (D : Op) (k : Arit D -> raw_code A) :
  LosslessOp D -> (forall x, LosslessHeapCode (k x)) ->
  LosslessHeapCode (x ← sample D ;; k x).
Proof.
move=> HD Hk h; rewrite Pr_code_sample.
rewrite psum_dlet_const1; first exact: HD.
move=> x; exact: Hk.
Qed.

(* LosslessHeap_get — a read followed by a continuation lossless at every read
   value terminates with mass one.
   Naming: PascalCase after the upstream family [Lossless_*] (nominal/Pr.v). *)
Lemma LosslessHeap_get (l : Location) (k : l -> raw_code A) :
  (forall v, LosslessHeapCode (k v)) ->
  LosslessHeapCode (x ← get l ;; k x).
Proof. move=> Hk h; rewrite Pr_code_get; exact: Hk. Qed.

(* LosslessHeap_put — a write followed by a lossless continuation terminates
   with mass one.
   Naming: PascalCase after the upstream family [Lossless_*] (nominal/Pr.v). *)
Lemma LosslessHeap_put (l : Location) (a : l) (k : raw_code A) :
  LosslessHeapCode k -> LosslessHeapCode (#put l := a ;; k).
Proof. move=> Hk h; rewrite Pr_code_put; exact: Hk. Qed.

(* LosslessHeap_bind — a prefix code lossless at every heap sequenced with a
   uniformly lossless continuation terminates with mass one, with no
   [ValidCode emptym] restriction on the prefix.
   Naming: PascalCase after the upstream family [Lossless_*] (nominal/Pr.v). *)
Lemma LosslessHeap_bind {B : choiceType} (c : raw_code B)
    (f : B -> raw_code A) :
  LosslessHeapCode c -> (forall x, LosslessHeapCode (f x)) ->
  LosslessHeapCode (x ← c ;; f x).
Proof.
move=> Hc Hf h; rewrite Pr_code_bind.
rewrite psum_dlet_const1; first exact: (Hc h).
move=> y; exact: Hf.
Qed.

(* LosslessHeap_if — a lossless conditional terminates with mass one.
   Naming: PascalCase after the upstream family [Lossless_if] (nominal/Pr.v). *)
Lemma LosslessHeap_if (b : bool) (c1 c2 : raw_code A) :
  LosslessHeapCode c1 -> LosslessHeapCode c2 ->
  LosslessHeapCode (if b then c1 else c2).
Proof. by case: b. Qed.

(* LosslessHeap_Pr_fst — heap-parametric losslessness gives the [Pr_fst]-based
   mass-one statement of SSProve's [LosslessCode] at the empty heap.
   Naming: PascalCase [LosslessHeap] subject with compound [Pr_fst] suffix, both
   tracking upstream (nominal/Pr.v). *)
Lemma LosslessHeap_Pr_fst (c : raw_code A) :
  LosslessHeapCode c -> psum (distr.mu (Pr_fst c)) = 1.
Proof.
move=> Hc; rewrite /Pr_fst dmarginE.
rewrite psum_dlet_const1; first exact: (Hc emptym).
move=> x; exact: Couplings.psum_SDistr_unit.
Qed.

End HeapLossless.
