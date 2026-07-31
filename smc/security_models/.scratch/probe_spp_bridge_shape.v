(* Probe P4 — claim S12: the disintegration shape of the SPP bridge.
   du2002/spp_simulator.v states privacy as a conditional-law equality
   (bob_view_cond_sim : Pr[ BobView = v | K = k ] = simulator ... v for
   every k with nonzero mass), while the kernel states it as a law
   factorization through >>=.  The bridge needs exactly one new lemma
   shape: conditional laws matching a kernel pointwise turn the joint
   pushforward into a bind.  This probe proves that shape in miniature
   on abstract finTypes over an abstract prior.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_spp_bridge_shape.v          *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba jfdist_cond.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.

Section bridge_shape.
Context {R : realType}.
Variables (T : finType) (P : R.-fdist T).
Variables (B K : finType).
Variable V : {RV P -> B}.   (* the view, as a random variable *)
Variable Kv : {RV P -> K}.  (* the conditioning data (inputs/outputs) *)
Variable k : K -> R.-fdist B.  (* the kernel (simulator \o allow-point) *)

(* S12: when the law of V conditioned on each mass-carrying fibre of Kv
   is the kernel at that fibre, the law of V is the law of Kv bound
   through the kernel. *)
Lemma cond_law_to_bind :
  (forall kk : K, `Pr[ Kv = kk ] != 0 ->
     forall v : B, `Pr[ V = v | Kv = kk ] = k kk v) ->
  `p_ V = `p_ Kv >>= k.
Proof.
move=> H; apply/fdist_ext => v.
rewrite fdistbindE -(fst_RV2 V Kv) fdist_fstE.
apply: eq_bigr => kk _; rewrite !dist_of_RVE.
case: (eqVneq `Pr[ Kv = kk ] 0) => [Hz|Hnz].
  by rewrite Hz mul0r pfwd1_domin_RV1.
by rewrite -H // cpr_eqE mulrC divfK.
Qed.

End bridge_shape.

(* FINDINGS
   1. The delivered declarations V : T -> B and Kv : T -> K do not
      elaborate under the repo's probability notation: pfwd1 recovers
      its distribution from the random-variable type, and RV_of reduces
      away, so the statement fails with
      Cannot infer the implicit parameter R of pfwd1.  They are now
      declared as {RV P -> B} and {RV P -> K}; the carriers are the same
      function types, so the claim is unchanged.
   2. No other adjustment was needed.  The conditional-probability lemma
      is cpr_eqE (proba line 2061),
      `Pr[ X = a | Y = b ] = `Pr[ [% X, Y] = (a, b) ] / `Pr[ Y = b ],
      the same one bob_view_cond_sim uses.  Zero-mass fibres are
      absorbed by pfwd1_domin_RV1 (proba line 1127),
      `Pr[ Y = b ] = 0 -> `Pr[ [% X, Y] = (a, b) ] = 0.  The marginal
      identity comes from fst_RV2 (proba line 932) and fdist_fstE, which
      is shorter than the reasoning_by_cases route since that lemma is
      phrased over fin_img and set-valued events.

   AXIOMS
   cond_law_to_bind rests on boolp.propositional_extensionality,
   boolp.functional_extensionality_dep and
   boolp.constructive_indefinite_description.  Those three are inherited
   from cpr_eqE, which carries exactly them in stock infotheo, so this
   probe adds no axiom of its own.

   MUTATION CHECKS, copies kept in this directory
   1. probe_spp_bridge_shape_mut1.v demands the hypothesis at one fixed
      fibre kk0 only; coqc exits 1 at line 35 with
      Error: The RHS of H (k kk0 _) does not match any subterm of the
      goal.
   2. probe_spp_bridge_shape_mut2.v flips the guard to
      `Pr[ Kv = kk ] = 0, leaving the kernel free on every mass-carrying
      fibre; coqc exits 1 at line 35 with
      Error: The LHS of cpr_eqE `Pr[ (_) = (_) | (_) = (_) ] does not
      match any subterm of the goal.
   3. probe_spp_bridge_shape_mut3.v compiles, and is meant to: over the
      uniform prior on 'I_2 with the view and the conditioning data both
      the identity and the constant Dirac kernel at ord0,
      counter_single_fibre proves the mutation of check 1 false.  The
      view law is uniform while the bind is the Dirac law at ord0, so
      the two disagree at lift ord0 ord0.                              *)
