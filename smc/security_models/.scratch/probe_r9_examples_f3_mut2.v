(* MUTATION 2 of examples_f3.v — the conditional-entropy equality genuinely
   fails at the coin-leak instance: coin_leak.centropy_view_honest_neq
   restated as the equality eq:smc:entropy asserts.  Rejected by coqc with
   exit status 1.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_r9_examples_f3_mut2.v            *)

From mathcomp Require Import all_boot all_order all_algebra reals lra.
Require Import realType_ext realType_ln fdist proba entropy.
Require Import finstoch statdist privacy_kernel examples_f3.

Import GRing.Theory Num.Theory Order.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section mutation.
Context {R : realType}.

(* Naming: <lemma under test>_mut is the intentional convention of the .scratch
   mutation files, marking a statement that coqc is expected to reject. *)
Lemma centropy_view_honest_eq_mut :
  `H( coin_leak.honest_rv | [% coin_leak.view_rv, coin_leak.allow_rv] )
  = `H( (coin_leak.honest_rv : {RV coin_leak.exec_law -> 'I_2})
        | coin_leak.allow_rv ) :> R.
Proof.
by rewrite coin_leak.centropy_view_honest0 coin_leak.centropy_honest_allow log2.
Qed.

End mutation.
