(* MUTATION 1 of examples_f3.v — the epsilon of the approximate verdict is
   tight: masking_verdicts.eps_privacy_biased restated at 12^-1 instead of
   6^-1.  Rejected by coqc with exit status 1.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_r9_examples_f3_mut1.v            *)

From mathcomp Require Import all_boot all_order all_algebra reals lra.
Require Import realType_ext realType_ln fdist proba entropy.
Require Import finstoch statdist privacy_kernel examples_f3.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.

Section mutation.
Context {R : realType}.

(* Naming: <lemma under test>_mut is the intentional convention of the .scratch
   mutation files, marking a statement that coqc is expected to reject. *)
Lemma eps_privacy_biased_mut :
  eps_privacy masking_verdicts.proj_adv_input id
              masking_verdicts.functionality
              (masking_verdicts.biased_mask : R.-fdist 'F_3)
              masking_verdicts.mask_view masking_verdicts.sim_mask
              12%:R^-1.
Proof.
move=> x.
rewrite masking_verdicts.view_law_maskE masking_verdicts.sim_view_maskE.
rewrite statdist_mask_chan.
rewrite /masking_verdicts.biased_mask /masking_verdicts.uniform_mask.
by rewrite biased_uniform_eps.
Qed.

End mutation.
