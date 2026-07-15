From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From mathcomp Require Import boolp reals realsum.
From SSProve.Crypt Require Import Package Pr.

Import GRing.Theory Num.Theory.
Notation R := SSProve.Crypt.Axioms.R.
Open Scope ring_scope.

Lemma dmargin_comp {T U V : choiceType} (g : T -> U) (h : U -> V)
    (mu : distr.distr R T) :
  distr.dmargin h (distr.dmargin g mu) = distr.dmargin (h \o g) mu.
Proof.
apply: SubDistr.distr_ext => y.
rewrite distr.dmarginE distr.dmarginE distr.dmarginE dlet_dlet_ext.
by apply: dlet_f_equal => z; rewrite dlet_unit_ext.
Qed.

Section probe.
Variables (T Mfin A : choiceType).
Variable mu0 : distr.distr R T.
Variable proj : T -> Mfin.
Variables (fa : Mfin -> A) (consb1 consb2 : Mfin) (msga msgb : A).

Goal
  distr.dmargin (fun t : (Mfin * Mfin * Mfin)%type =>
      (fa t.1.1, fa t.1.2, fa t.2))
    (distr.dmargin (fun g : Mfin => (g, consb1, consb2))
       (distr.dmargin proj mu0))
  = distr.dmargin (fun g : Mfin => (fa g, fa consb1, fa consb2))
       (distr.dmargin proj mu0).
Proof.
rewrite dmargin_comp.
rewrite [in LHS]distr.dmarginE [in RHS]distr.dmarginE.
apply: eq_dlet => g /=.
Abort.

End probe.
