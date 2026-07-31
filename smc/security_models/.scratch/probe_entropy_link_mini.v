(* Probe D1 — the Iwamoto-direction miniature for entropy_link.v,
   deliberately scoped to a DETERMINISTIC functionality (F = dirac F0):
   for randomized F the view-only triangle does not imply the entropy
   equality (the view correlates with honest outputs through the
   ancilla), which is a spec-level scope decision recorded in the
   design.  This probe tests the deterministic case's proof route in
   miniature:
     perfect privacy (triangle at every input)
       ==> conditional independence  honest _|_ view | allowed
       ==> centropy equality  H(honest | view, allowed) = H(honest | allowed)
   over a joint space  X * Omega  with prior  mu `x P_Omega.
   Goals of the probe:
   E1  pin the infotheo names: conditional independence on RVs
       (graphoid.v / proba.v: `P |= X _|_ Y | Z`), conditional entropy
       of RVs and the lemma(s) linking CI to centropy equality
       (information_theory: centropy / cond_entropy / cmi; Search).
   E2  Qed the miniature at abstract finTypes if the route exists as
       library lemmas, else at the smallest concrete carrier that
       forces the route; if a step has NO library support, report
       NO-GO for that step with the exact missing statement — that
       missing lemma becomes implementation work in the plan.
   Both targets are GO at abstract finTypes; the findings, axioms and
   mutation checks are recorded at the end of this file.
   Compile from repo root:
     /Users/cheng-huiweng/Projects/coq/_opam/bin/coqc -R . infotheo \
       smc/security_models/.scratch/probe_entropy_link_mini.v        *)

From mathcomp Require Import all_ssreflect all_algebra reals.
Require Import realType_ext realType_ln ssr_ext bigop_ext fdist proba.
Require Import jfdist_cond entropy graphoid.
Require Import extra_proba extra_entropy.

Import GRing.Theory Num.Theory.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
Local Open Scope ring_scope.
Local Open Scope fdist_scope.
Local Open Scope proba_scope.
Local Open Scope entropy_scope.

Section entropy_link_mini.
Context {R : realType}.
Variables X Omega Bv Al : finType.   (* inputs, ancilla, view, allowed *)
Variable mu : R.-fdist X.
Variable P_Omega : R.-fdist Omega.
Variable view_at : X * Omega -> Bv.
Variable allow0 : X -> Al.           (* deterministic allowed info *)
Variable Sim : Al -> R.-fdist Bv.

(* The joint prior on the execution context. *)
Definition d : R.-fdist (X * Omega)%type := (mu `x P_Omega)%fdist.

(* RVs on the execution context. *)
Definition view_rv : {RV d -> Bv} := view_at.
Definition input_rv : {RV d -> X} := fst.
Definition allow_rv : {RV d -> Al} := allow0 \o fst.

(* Per-input triangle, deterministic-functionality form: at every input
   of positive mass the conditional view law is Sim at the allowed
   value.  (This is what perfect_privacy specializes to when
   F = dirac F0; stated here directly to keep the miniature small.) *)
Hypothesis triangle :
  forall x : X, `Pr[ input_rv = x ] != 0 ->
  forall v : Bv, `Pr[ view_rv = v | input_rv = x ] = Sim (allow0 x) v.

(* The joint law of an RV and a deterministic function of it is the
   law of the RV cut down to the fibre of that function. *)
Lemma pfwd1_pair_det (U TA TB : finType) (P : R.-fdist U)
    (W : {RV P -> TA}) (Z : {RV P -> TB}) (g : TA -> TB) :
  (forall u, Z u = g (W u)) ->
  forall w z, `Pr[ [% W, Z] = (w, z) ] = (g w == z)%:R * `Pr[ W = w ].
Proof.
move=> Hg w z; rewrite !pfwd1E /Pr.
case: (eqVneq (g w) z) => [<-|H].
  rewrite mul1r; apply: eq_bigl => u.
  by rewrite !inE /= xpair_eqE Hg; case: eqP => [->|]; rewrite ?eqxx.
rewrite mul0r; apply: big_pred0 => u.
by rewrite !inE /= xpair_eqE Hg; case: eqP => [->|] //=; rewrite (negbTE H).
Qed.

(* The joint law of the view and the input is the simulator law at the
   allowed value weighted by the input law. *)
Lemma pfwd1_view_input v x :
  `Pr[ [% view_rv, input_rv] = (v, x) ]
  = Sim (allow0 x) v * `Pr[ input_rv = x ].
Proof.
have [Hx|Hx] := eqVneq (`Pr[ input_rv = x ]) 0.
  by rewrite Hx mulr0 pfwd1_domin_RV1.
by have := triangle Hx v; rewrite cpr_eqE => <-; rewrite divfK.
Qed.

(* E1/E2 target 1: the triangle gives conditional independence of the
   view and the input given the allowed information. *)
Lemma triangle_cinde : d |= view_rv _|_ input_rv | allow_rv.
Proof.
pose f (x : X) (a : Al) : R := (allow0 x == a)%:R * `Pr[ input_rv = x ].
pose g (a : Al) (v : Bv) : R := Sim a v.
apply: (cinde_RV_factor (f := f) (g := g)) => v x a.
rewrite (pfwd1_pair_det (g := fun p : Bv * X => allow0 p.2)) //.
rewrite /= pfwd1_view_input /f /g.
case: (eqVneq (allow0 x) a) => [->|H].
  by rewrite -mulrA [_ * Sim a v]mulrC mulrA.
by rewrite mulr0n !mul0r.
Qed.

(* E1/E2 target 2: conditioning the input on the view on top of the
   allowed information leaves its conditional entropy unchanged. *)
Lemma cinde_centropy_eq :
  `H( input_rv | [% view_rv, allow_rv] ) = `H( input_rv | allow_rv ).
Proof. exact: extra_entropy.cinde_centropy_eq triangle_cinde. Qed.

End entropy_link_mini.

(* FINDINGS

   1. Conditional independence of RVs is `cinde_RV`, notation
      `P |= X _|_ Y | Z` (proba.v lines 2302/2316), over `A B C : eqType`.
      `cinde_rv` is a deprecated parsing-only alias (proba.v line 2319).
      graphoid.v only re-uses the notation, it does not define it, so
      the probe's guess that the notation lives in graphoid.v is off by
      one file; graphoid.v supplies the axioms (symmetry, decomposition,
      weak_union, contraction, intersection).  The probe statement of
      target 1 needed NO change.

   2. Conditional entropy of RVs is `centropy_RV`, notation
      `H( Y | X )` in entropy_scope (entropy.v lines 418/422), with the
      per-value form `centropy1_RV`, notation `H[ Y | X = a ]`
      (entropy.v lines 416/421).  `cond_entropy` / `cond_entropy1` are
      deprecated parsing-only aliases (entropy.v lines 369/371).  Using
      the notation needs `Local Open Scope entropy_scope.`, which the
      probe skeleton did not open; that line is the only spelling
      adaptation made to the header.

   3. The CI-to-centropy link EXISTS and is named exactly as the probe's
      target: `cinde_centropy_eq` in dumas2017dual/lib/extra_entropy.v
      line 126,
        Lemma cinde_centropy_eq :
          P |= X _|_ Y | Z -> `H(Y | [% X, Z]) = `H(Y | Z).
      Instantiating X := view_rv, Y := input_rv, Z := allow_rv turns
      target 1 into exactly the shape the probe asked for, with the pair
      already in the order [% view_rv, allow_rv], so no
      `centropy_RV_fdistA` swap is needed.  Target 2 is therefore a
      one-line consequence of target 1 and is NOT implementation work.
      Because the probe keeps the target name, the library constant is
      referred to by its qualified name inside the proof.

   4. The link is NOT in information_theory/.  entropy.v stops at
      `centropy_RV_comp0` (line 498), `cPr_centropy_RV_comp` (line 581)
      and `centropy_RV_contraction` (line 831); the CI-shaped statement
      is project-local in dumas2017dual/lib/extra_entropy.v, routed
      through `cinde_cond_mutual_info0` (same file, line 73),
        P |= X _|_ Y | Z -> cond_mutual_info `p_[% X, Y, Z] = 0,
      and `cond_mutual_info` / `cond_mutual_infoE` from entropy.v.  A
      security_models file taking this route imports
      dumas2017dual/lib/extra_entropy.v across project directories, or
      the two lemmas get upstreamed.

   5. A second, weaker route exists in du2002/spp_entropy.v line 218,
        Lemma cpr_centropy :
          (forall y1 y2 y3, `Pr[ [% Y2, Y3] = (y2, y3) ] != 0 ->
             `Pr[ Y1 = y1 | [% Y2, Y3] = (y2, y3) ]
             = `Pr[ Y1 = y1 | Y2 = y2 ]) ->
          `H( Y1 | [% Y2, Y3]) = `H( Y1 | Y2).
      It is driven by a conditional-probability removal hypothesis rather
      than by `cinde_RV`, and its conclusion carries the pair in the order
      [% allow_rv, view_rv], so it needs `centropy_RV_fdistA` (entropy.v
      line 551) to reach the probe's orientation.  Finding 3 is shorter
      and is the route taken.

   6. Target 1 is proved through `cinde_RV_factor`
      (dumas2017dual/lib/extra_proba.v line 529),
        (forall x y z, `Pr[ [% X, Y, Z] = (x, y, z) ] = f y z * g z x) ->
        P |= X _|_ Y | Z,
      which avoids identifying either conditional marginal.  The
      factorisation is f x a = (allow0 x == a)%:R * `Pr[ input_rv = x ]
      and g a v = Sim a v.  Without it the proof has to evaluate
      `Pr[ view_rv = v | allow_rv = a ] = Sim a v by a law-of-total-
      probability sum over the input fibre, using `reasoning_by_cases`
      (proba.v line 2266) or `marg_out_Y` / `marg_Z_X`
      (extra_proba.v lines 494/516).

   7. The probe's product prior mu `x P_Omega is never used: the two
      targets hold for an arbitrary `d : R.-fdist (X * Omega)` once the
      triangle is assumed.  The proof also never uses that Sim lands in
      fdists, only that it is an Al-indexed family of Bv-indexed reals.

   8. Only one auxiliary fact is not in the libraries, `pfwd1_pair_det`
      above: the joint law of an RV with a deterministic function of it.
      `pfwd1_diag` (proba.v line 988) covers the identity function only.
      It is six lines and is the sole new statement this route needs.

   NOTHING IS MISSING FROM THE LIBRARY for either target.

   AXIOMS
   `Print Assumptions` on `triangle_cinde` and on `cinde_centropy_eq`
   returns, for both, exactly boolp.propositional_extensionality,
   boolp.functional_extensionality_dep and
   boolp.constructive_indefinite_description.  Those three are inherited
   from cpr_eqE and the entropy layer, which carry exactly them in stock
   infotheo, so this probe adds no axiom of its own.

   MUTATION CHECKS, copies kept in this directory
   1. probe_entropy_link_mini_mut1.v demands the triangle at one fixed
      input x0 only; coqc exits 1 at line 58 in `pfwd1_view_input` with
      Error: The term "Hx" has type
      is_true (`Pr[ (input_rv) = (x) ] != 0) while it is expected to
      have type is_true (`Pr[ (input_rv) = (x0) ] != 0).
   2. probe_entropy_link_mini_mut2.v drops the triangle hypothesis
      altogether; coqc exits 1 at line 59 in `pfwd1_view_input` with
      Error: The variable triangle was not found in the current
      environment.
   3. probe_entropy_link_mini_mut3.v compiles, and is meant to: over the
      uniform prior on bool with a trivial ancilla, the view equal to
      the input, the allowed information constant and the simulator the
      Dirac law at true, counter_triangle_single proves the mutation-1
      hypothesis at the input true and counter_single_input proves the
      mutation-1 conclusion false.  Conditional independence given a
      constant is unconditional independence (cinde_RV_unit, proba.v
      line 2343), and at (true, true, tt) it would force
      2^-1 = 2^-1 * 2^-1.                                            *)
