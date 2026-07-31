(* SOUNDNESS AUDIT — adjudication of spec §6 (Iwamoto-direction scope),
   side (a): for a RANDOMIZED functionality the view-only privacy
   triangle does NOT imply the conditional independence behind
   eq:smc:entropy once the honest delivered output is included.
   Concrete instance: a single (trivial) input, a uniform-bit ancilla,
   the protocol delivers the honest party's output y_h = omega and ALSO
   shows omega to the adversary (view = omega); the allowed information
   is trivial.  Then:
     - view_only_triangle : the per-input triangle of probe D1 holds
       (the view law at the unique input IS Sim at the allowed value);
     - not_cinde_honest   : the conditional independence
       view _|_ honest-output | allowed FAILS (1/2 <> 1/4), and
     - centropy_view_honest0 : H(honest | view, allowed) = 0, whereas
       H(honest | allowed) = H(uniform bit) = log 2 <> 0 (the honest
       output is uniform and the allowed information is constant), so
       the conditional-entropy equality eq:smc:entropy with the honest
       output on the left is FALSE at this instance.
   Consequence for the spec: the deterministic-F scoping of §6 is
   load-bearing, not an over-caution; the randomized case genuinely
   needs the joint (view, output) simulation notion.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/audit_snd_randomized_F.v          *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext fdist proba.
Require Import entropy.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section randomized_counterexample.
Context {R : realType}.

Definition P2 : R.-fdist 'I_2 := @fdist_uniform R _ 1 (card_ord 2).
Definition d : R.-fdist ('I_1 * 'I_2)%type := ((fdist1 ord0) `x P2)%fdist.

Definition view_rv   : {RV d -> 'I_2} := snd.  (* adversary sees omega  *)
Definition honest_rv : {RV d -> 'I_2} := snd.  (* honest output = omega *)
Definition input_rv  : {RV d -> 'I_1} := fst.
Definition allow_rv  : {RV d -> 'I_1} := fst.  (* allowed info: trivial *)
Definition allow0 : 'I_1 -> 'I_1 := id.
Definition Sim (a : 'I_1) : R.-fdist 'I_2 := P2.

Lemma dE u : d u = 2%:R^-1.
Proof.
case: u => a b; rewrite /d fdist_prodE (ord1 a) fdist1xx mul1r.
by rewrite /P2 fdist_uniformE card_ord.
Qed.

(* Every 'I_1-valued RV is full-mass. *)
Lemma pr_ord1 (Z : {RV d -> 'I_1}) (t : 'I_1) : `Pr[ Z = t ] = 1.
Proof.
rewrite pfwd1E.
suff -> : finset (Z @^-1 t) = [set: ('I_1 * 'I_2)%type] by rewrite Pr_setT.
by apply/setP => u; rewrite !inE (ord1 (Z u)) (ord1 t) eqxx.
Qed.

(* Point-mass events for the pairings used below. *)
Lemma pr_view_input (v : 'I_2) (x : 'I_1) :
  `Pr[ [% view_rv, input_rv] = (v, x) ] = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% view_rv, input_rv] @^-1 (v, x))
          = [set (ord0, v) : 'I_1 * 'I_2] by rewrite Pr_set1 dE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /view_rv /input_rv /=.
by rewrite (ord1 a) (ord1 x) !eqxx andbT.
Qed.

Lemma pr_view_allow :
  `Pr[ [% view_rv, allow_rv] = (ord0, ord0) ] = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% view_rv, allow_rv] @^-1 (ord0, ord0))
          = [set (ord0, ord0) : 'I_1 * 'I_2] by rewrite Pr_set1 dE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /view_rv /allow_rv /=.
by rewrite (ord1 a) !eqxx andbT.
Qed.

Lemma pr_honest_allow :
  `Pr[ [% honest_rv, allow_rv] = (ord0, ord0) ] = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% honest_rv, allow_rv] @^-1 (ord0, ord0))
          = [set (ord0, ord0) : 'I_1 * 'I_2] by rewrite Pr_set1 dE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /honest_rv /allow_rv /=.
by rewrite (ord1 a) !eqxx andbT.
Qed.

Lemma pr_view_honest_allow :
  `Pr[ [% [% view_rv, honest_rv], allow_rv] = ((ord0, ord0), ord0) ]
  = 2%:R^-1.
Proof.
rewrite pfwd1E.
suff -> : finset ([% [% view_rv, honest_rv], allow_rv]
                    @^-1 ((ord0, ord0), ord0))
          = [set (ord0, ord0) : 'I_1 * 'I_2] by rewrite Pr_set1 dE.
apply/setP => -[a b]; rewrite !inE !xpair_eqE /view_rv /honest_rv /allow_rv /=.
by rewrite (ord1 a) !eqxx andbb andbT.
Qed.

(* Side (a), half 1: the view-only per-input triangle of probe D1 HOLDS
   at this randomized functionality (statement shape identical to the
   probe's Hypothesis triangle). *)
Lemma view_only_triangle (x : 'I_1) : `Pr[ input_rv = x ] != 0 ->
  forall v : 'I_2, `Pr[ view_rv = v | input_rv = x ] = Sim (allow0 x) v.
Proof.
move=> _ v; rewrite cpr_eqE pr_ord1 divr1 pr_view_input.
by rewrite /Sim /P2 fdist_uniformE card_ord.
Qed.

(* Side (a), half 2: the conditional independence that the Iwamoto
   direction needs once the honest output joins the left side FAILS. *)
Lemma not_cinde_honest : ~ (d |= view_rv _|_ honest_rv | allow_rv).
Proof.
move=> H; have twoNZ : (2%:R : R) != 0 by rewrite pnatr_eq0.
have := H ord0 ord0 ord0.
rewrite !cpr_eqE !pr_ord1 !divr1.
rewrite pr_view_honest_allow pr_view_allow ?pr_honest_allow.
move/(congr1 (fun t : R => 2%:R * t)).
rewrite mulfV// mulrA mulfV// mul1r => /eqP.
by rewrite eq_sym invr_eq1 pnatr_eq1.
Qed.

(* The entropy side, left half: conditioned on (view, allowed) the honest
   output has zero conditional entropy — the view determines it. *)
Lemma centropy_view_honest0 :
  `H( honest_rv | [% view_rv, allow_rv] ) = 0.
Proof. exact: (centropy_RV_comp0 [% view_rv, allow_rv] fst). Qed.

End randomized_counterexample.
