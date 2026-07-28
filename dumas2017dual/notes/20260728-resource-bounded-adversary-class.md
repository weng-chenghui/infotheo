# Resource-bounded adversary class and the `computational/` assumption surface

Date: 2026-07-28
Branch base: `itp2026-dumas2017dual`
Status: design approved, not implemented

## Problem

`enc_ind_cpa_real_or_zero` (`homomorphic_encryption/indcpa_ror.v:256`) quantifies over
`reduction : raw_package` with no restriction beyond well-typedness. SSProve's
`ValidPackage` constrains interfaces, locations and imports. It says nothing about
computational resources. The axiom therefore asserts the IND-CPA advantage bound
against computationally unbounded adversaries.

For any correct encryption scheme this forces `epsilon_cpa AHE` to be close to 1.
`Renc` is a `finType` and `pkey_of_party` is bound before `reduction` is quantified,
so a `raw_package` can hard-code the public key and decide, by finite search over
`#|Renc|`, whether a ciphertext `c` satisfies `c = Enc(pk, m; r)` for some `r`. That
distinguisher achieves advantage close to 1. Every `_ <= 2 * epsilon_cpa AHE` bound is
then vacuous, and so is `1/m + 2 * epsilon_cpa AHE`.

`indcpa_ror.v:233-240` already records the same argument for the cross-scheme case,
which is why `epsilon_cpa` is indexed by `AHEncType`. Indexing does not close the hole,
because the argument goes through inside a fixed scheme once the adversary class is
unrestricted.

A computational security theorem is meant to quantify over resource-bounded
adversaries. The unrestricted quantifier is a missing hypothesis, not extra strength.

## Second, unrelated problem found in the same area

`dsdp_adm` (`dumas2017dual/dsdp/simulation/dsdp_simulator.v:225`) and the `adm`
parameter it instantiates (`smc/ssprove_ext_simulator.v:36`) are named for
admissibility, which in cryptography reads as the adversary class an assumption is
asserted against. Their content is location disjointness:

```coq
Definition dsdp_adm (LA : Locations) (A : raw_package) : Prop :=
  fseparate LA (protocol_state t_msg) /\
  fseparate LA (locs (oracle_real_pkg ...)) /\
  fseparate LA (locs (oracle_zero_pkg ...)).
```

The name points at the wrong concept, `adm` is a semantic-stripping abbreviation, and
the `raw_package` argument is never used in the body. Introducing a genuine
computational predicate while leaving this one named "admissible" would put two
unrelated notions of admissibility in the same development.

## Goals

1. Move the repository's entire global-assumption surface into a new `computational/`
   directory.
2. Guard `enc_ind_cpa_real_or_zero` with an opaque `resource_bounded` predicate and
   thread that hypothesis to every theorem that consumes the axiom.
3. Rename `adm` / `dsdp_adm` to say what they check, and drop the unused argument.

## Non-goals

- Defining `resource_bounded`. It stays an opaque `Parameter`.
- Formalizing polynomial time, circuit size, query counts, or any machine model.
- Making any bound numerically non-vacuous. No number becomes meaningful until someone
  instantiates `resource_bounded`.
- Touching the information-theoretic leg. `dsdp_alice_guess_V2_zero_le` and its fiber
  chain are proven for arbitrary predictors under structural side conditions only.
- Touching `dsdp_simulator_factorization`, which is a perfect `≈₀` equivalence.

## What is and is not lost

The guarded statement subsumes the current one. `resource_bounded` is an opaque
`Parameter`, so instantiating it at `fun _ => True` makes the guarded statement
definitionally equal to the current statement. No obtainable result is excluded. The
change adds a knob, and the apparent weakening exists only relative to a chosen
instantiation.

Behaviour per theorem shape:

| Shape | Example | Effect |
|---|---|---|
| Upper bound consuming the axiom | `dsdp_alice_guess_V2_real_le`, `dsdp_alice_simulation_secure` | Hypothesis added, proof unchanged apart from threading |
| Lower bound exploiting the axiom | `epsilon_cpa_idealized_ge1` | Needs `resource_bounded idealized_distinguisher` as a new assumption |
| Independent of the axiom | `dsdp_alice_guess_V2_zero_le`, `dsdp_simulator_factorization` | Statement and proof unchanged |

Real costs:

1. Assumption surface grows by one `Parameter` and three `Axiom`s. Every headline's
   `Print Assumptions` gains four entries.
2. Section-level hypotheses (`shim_bounded`, `challenger_bounded`,
   `predictor_resource_bounded`) are distributed across files with no central
   inventory. A future instantiation must locate all of them.
3. Seventeen lemmas across five compiled files gain an argument, plus `adv_sim_le` and
   its two helper lemmas in `smc/ssprove_ext_simulator.v`. Every `apply:` and `exact:`
   argument list at their call sites shifts.
4. `epsilon_cpa_idealized_ge1` becomes conditional, weakening the justification for
   indexing `epsilon_cpa` by scheme.
5. Headline signatures, already long, gain one more hypothesis.
6. Rename churn in three files, and the arity drop forces the destructuring pattern in
   `dsdp_adv_sim_le`'s proof to change.
7. Blueprint coverage checker must be rerun. Thesis and blueprint prose that says "any
   adversary" about these theorems must say "any resource-bounded adversary".

## Design

### `computational/resource_bounded.v` (new)

```coq
Parameter resource_bounded : raw_package -> Prop.

Axiom resource_bounded_link : forall A B,
  resource_bounded A -> resource_bounded B -> resource_bounded (A ∘ B).
Axiom resource_bounded_par : forall A B,
  resource_bounded A -> resource_bounded B -> resource_bounded (par A B).
Axiom resource_bounded_ID : forall I, resource_bounded (ID I).
```

Only the combinator closure properties are axiomatized. They hold under any reading of
a resource class. Facts of the form "this protocol package is resource-bounded" are
stated as section hypotheses at the sites that need them, so a future instantiation
checks them one by one instead of inheriting them as global axioms.

Name rationale: not abbreviated, reads as a predicate in the MathComp idiom
(`injective f`, `bijective f`), names the kind of restriction without committing to a
machine model. `efficient` was rejected because it reads as PPT in the literature and
the predicate is deliberately model-agnostic. `admissible` was rejected because
SSProve-adjacent usage reads it as interface validity, which `ValidPackage` already
covers. No identifier clash in SSProve, MathComp, or this repository.

### `computational/indcpa_assumption.v` (new, receives moved declarations)

Receives `epsilon_cpa` and `enc_ind_cpa_real_or_zero` from `indcpa_ror.v:241` and
`:256`. The axiom gains the guard:

```coq
Axiom enc_ind_cpa_real_or_zero :
  forall (AHE : AHEncType) ... (reduction : raw_package),
    resource_bounded reduction ->
    AdvantageE (oracle_encrypt_real ...) (oracle_encrypt_zero ...) reduction
    <= epsilon_cpa AHE.
```

`indcpa_ror.v` keeps only the oracle constructions. `End indcpa_ror.` is at line 231
and both declarations sit after it, so the file already separates along this line.

Dependency consequence: `homomorphic_encryption/indcpa_ror.v` no longer needs
`resource_bounded`, so the `homomorphic_encryption/` subtree acquires no new
dependency. All new edges originate in `computational/` and `smc/`.

`_CoqProject` ordering:

- `computational/resource_bounded.v` before `smc/ssprove_ext_simulator.v` (line 102)
- `computational/indcpa_assumption.v` after `homomorphic_encryption/indcpa_ror.v`
  (line 123), because the axiom statement needs the oracle definitions

Files that must add an import of `computational/indcpa_assumption`:
`dsdp_main.v`, `dsdp_simulator.v`, `dsdp_indcpa_advantage.v`, `dsdp_game_derivation.v`,
`idealized_indcpa.v`.

### Rename

| Before | After | Type before | Type after |
|---|---|---|---|
| `adm` (`smc/ssprove_ext_simulator.v:36`) | `locs_disjoint` | `Locations -> raw_package -> Prop` | `Locations -> Prop` |
| `dsdp_adm` (`dsdp_simulator.v:225`) | `dsdp_locs_disjoint` | `Locations -> raw_package -> Prop` | `Locations -> Prop` |

Occurrences: `smc/ssprove_ext_simulator.v` 9, `dsdp_simulator.v` 5 plus the
destructuring in `dsdp_adv_sim_le`'s proof, `probe_p5_skeletons.v` 11. The probe file
is not in `_CoqProject` and is updated only to avoid leaving contradictory vocabulary.

Blueprint references `dsdp_adv_sim_le` (`security.tex:196`), whose name does not
change. No `\rocq{}` edit is required.

### `adv_sim_le` states both conditions directly

```coq
Context (E : Interface) (locs_disjoint : Locations -> Prop).

Definition adv_sim_le (Real Ideal Sim : raw_package) (eps : R) : Prop :=
  forall (LA : Locations) (A : raw_package),
    ValidPackage LA E A_export A ->
    locs_disjoint LA -> resource_bounded A ->
    AdvantageE Real (Sim ∘ Ideal) A <= eps.
```

An earlier draft kept a single generic hook parameter covering both conditions. It was
dropped because a deliberately contentless parameter has no informative name, and
because DSDP instantiates it exactly one way. `locs_disjoint` stays a parameter since
the location sets compared are protocol-specific. `resource_bounded` is used directly
since it is opaque and there is nothing to parameterize.

`adv_sim_le` can no longer state an information-theoretic simulation result under a
non-trivial `resource_bounded`. This is not a loss of reachable results, by the
subsumption argument above.

### Threading inventory

Axiom application sites, two only:

- `symbolic_game/dsdp_game_code.v:909` in `advantage_hop`
- `indcpa_hopping/dsdp_indcpa_advantage.v:286` in `advantage_hop_leak_S`

At both sites the axiom is applied to `A ∘ shim`, not to `A`, so the discharge is:

```coq
apply: (enc_ind_cpa_real_or_zero ...).
by apply: resource_bounded_link; [exact: A_bounded | exact: shim_bounded].
```

Lemmas gaining a `resource_bounded` hypothesis:

| File | Lemmas |
|---|---|
| `symbolic_game/dsdp_game_code.v` | `advantage_hop` (886), `advantage_sum_ladder_le` (930), `advantage_le` (973), `advantage_gc_dsdp` (1064) |
| `symbolic_game/dsdp_game_derivation.v` | `dsdp_indcpa_secrecy` (691) |
| `indcpa_hopping/dsdp_indcpa_advantage.v` | `dsdp_advantage_derived` (63), `advantage_hop_leak_S` (249), `advantage_sum_ladder_le_leak_S` (294), `advantage_le_leak_S` (329), `dsdp_advantage_derived_leak_S` (405) |
| `simulation/dsdp_simulator.v` | `dsdp_adv_sim_le` (279) |
| `dsdp/dsdp_main.v` | `dsdp_alice_view_advantage_le` (128), `dsdp_alice_guess_advantage_le` (726), `dsdp_alice_guess_V2_real_le` (756), `dsdp_alice_unpredictability_entropy_ge` (789), `dsdp_alice_simulation_secure` (850), `dsdp_alice_view_statdist_le` (903) |

`advantage_self_zero` (`dsdp_game_code.v:955`) does not apply the axiom and is
untouched.

In `Section dsdp_alice_guess` the predictor is a section variable, so adding

```coq
Hypothesis predictor_resource_bounded : resource_bounded (pack predictor).
```

is enough. Rocq generalizes a section hypothesis only over declarations that use it,
so `dsdp_alice_guess_V2_zero_le` keeps its current type unchanged while the
axiom-consuming lemmas gain the argument. The asymmetry between the two legs is
recorded automatically.

Narrowing the `1/m` bound from the unrestricted to the restricted adversary class
requires no lemma and no assumption. `dsdp_alice_guess_V2_zero_le` quantifies over
predictors with no class restriction, so it applies to any particular predictor. In
type theory this is weakening, that is, adding an unused hypothesis.

## Phases

Each phase builds clean and is committed before the next begins.

**Phase 0. Pure move.** Create `computational/`, move `epsilon_cpa` and
`enc_ind_cpa_real_or_zero` out of `indcpa_ror.v` unchanged, update `_CoqProject` and
the five importing files. No statement changes. Verifiable by compilation alone.

**Phase 1. Rename.** `adm` to `locs_disjoint`, `dsdp_adm` to `dsdp_locs_disjoint`,
arity dropped, destructuring in `dsdp_adv_sim_le` adjusted, probe file updated.

**Phase 2. Introduce the predicate and thread it unused.** Add
`computational/resource_bounded.v`. Add `resource_bounded` hypotheses to the seventeen
lemmas, add `resource_bounded A` to `adv_sim_le`, and add the section hypotheses.
Nothing consumes them yet. The build stays green, which is what makes this phase
mechanically checkable.

**Phase 3. Guard the axiom.** Add the guard to `enc_ind_cpa_real_or_zero`, discharge it
at the two application sites via `resource_bounded_link`, and add
`resource_bounded idealized_distinguisher` to `epsilon_cpa_idealized_ge1`.

**Phase 4. Verification and documentation.** `Print Assumptions` on every headline,
blueprint coverage rerun, blueprint and thesis wording scan.

Phase ordering rationale: threading before guarding keeps every intermediate state
compilable. Guarding first would break the whole downstream at once.

## Verification

- Full-tree `make` under the local `~/Projects/coq/_opam` switch, per phase.
- `Print Assumptions` on each headline in `dsdp_main.v`. Every assumption must resolve
  to a declaration in `computational/`. Anything else is a defect. This check is the
  payoff of the new directory and is exercised from the first phase that adds an
  assumption.
- `dumas2017dual/blueprint/check_coverage.py` returns OK.
- Confirm `dsdp_alice_guess_V2_zero_le` and `dsdp_simulator_factorization` have
  byte-identical statements before and after.

## Open items

- Whether `resource_bounded` should also guard any future non-IND-CPA assumption is out
  of scope until a second assumption exists.
- The section hypotheses have no central inventory. If their number grows beyond the
  three anticipated, collecting them into a record is worth reconsidering.
