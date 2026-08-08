# Rocq formalization request: PGL(2,7) four-subset orbit split

Date: 2026-08-08

Request path: `docs/superpowers/requests/2026-08-08-pgl27-orbit-split-ROCQ-formalization-spec.md`

Status: REQUEST ONLY. No Rocq source has been changed for this request. The
formalization tool must probe the statements before it writes an implementation
plan.

## 1. Goal

Prove that the two Boolean fibers of `subset_class` on four-subsets of `'I_8`
are exactly the two orbits of the existing shuffle group `pgg_G pgl27_M`.

The current development proves that the classifier is invariant and that its
two fibers have sizes 28 and 42. It does not prove that either fiber is a single
orbit. Invariance and cardinality alone are not enough because one fiber could
be a union of smaller orbits.

This request closes only that gap.

## 2. Scope

Primary file to modify:

`pgg-smc/instances/pgl27/pgl27_orbit.v`

The formalization tool may modify `pgl27_group.v` only if it must expose an
existing local certificate for reuse. It must explain why a local construction
in `pgl27_orbit.v` is not enough before doing so.

The result concerns the concrete generated permutation group used by the
protocol:

```coq
pgg_G pgl27_M
```

The carrier is:

```coq
{set 'I_8}
```

restricted to subsets of cardinality four. The action on a subset is the
existing permutation image `g @: S`.

## 3. Required results

### 3.1 Public subset-level invariance

Expose the invariant that is currently available only through local helper
lemmas. The intended statement shape is:

```coq
Lemma subset_class_invariant
    (g : pgg_gT pgl27_M) (S : {set 'I_8}) :
  g \in pgg_G pgl27_M ->
  subset_class (g @: S) = subset_class S.
```

The final name may change only to satisfy the repository's MathComp naming
rules. Record any change in the completion report.

### 3.2 Orbit completeness of the classifier

Prove that equal classifier values are equivalent to reachability under the
shuffle group when both subsets have cardinality four. The intended statement
shape is:

```coq
Lemma subset_class_orbit (S T : {set 'I_8}) :
  #|S| = 4 -> #|T| = 4 ->
  (subset_class S = subset_class T <->
   exists g : pgg_gT pgl27_M,
     g \in pgg_G pgl27_M /\ T = g @: S).
```

Both directions are required.

The reverse direction should use `subset_class_invariant`. The forward
direction is the missing mathematical content. A theorem that proves only
invariance, equal cardinalities, or existence for the two encoder decks does
not satisfy this requirement.

An equivalent pair of transitivity lemmas, one for each Boolean fiber, is
acceptable if the tool also derives the stated equivalence as a public
corollary.

### 3.3 Paper-facing orbit split

The completed formalization must support the following statement without any
informal step:

> The action of the protocol's PGL(2,7) shuffle group on the four-subsets of
> the projective line has one equianharmonic orbit of size 28 and one harmonic
> orbit of size 42.

The paper may cite several Rocq declarations for this one theorem. The expected
set is:

```text
subset_class_orbit
orbit_class_split
orbit_class_split_complement
```

The existing count lemmas need not be restated. Change them only if a statement
must be generalized for the orbit proof.

## 4. Existing facts to reuse

All paths below are live paths in this repository.

| Identifier | File | Available fact |
|---|---|---|
| `pgl27_3transitive` | `pgg-smc/instances/pgl27/pgl27_group.v` | The generated group acts 3-transitively on `'I_8`. |
| `pgl27_rho_im` | `pgg-smc/instances/pgl27/pgl27_group.v` | The image of the protocol morphism is the generated group. |
| `subset_class` | `pgg-smc/instances/pgl27/pgl27_orbit.v` | Boolean classifier on subsets of `'I_8`. |
| `orbit_class_invariant` | `pgg-smc/instances/pgl27/pgl27_orbit.v` | Deck-level classifier invariance under the shuffle group. |
| `orbit_encodeK` | `pgg-smc/instances/pgl27/pgl27_orbit.v` | Both Boolean classes have explicit encoded representatives. |
| `orbit_class_split` | `pgg-smc/instances/pgl27/pgl27_orbit.v` | The equianharmonic fiber contains 28 four-subsets. |
| `orbit_class_split_complement` | `pgg-smc/instances/pgl27/pgl27_orbit.v` | The harmonic fiber contains 42 four-subsets. |

The local lemmas `stabpP` and `G_sub_stabp` already contain the proof needed for
the public subset-level invariance result.

## 5. Recommended proof boundary

Prefer a finite, axiom-free reachability certificate over a new abstract theory
of projective geometry. The development already represents the group and all
70 four-subsets as finite objects.

A suitable proof may do either of the following:

1. Choose one explicit representative in each Boolean fiber. Certify that every
   four-subset in the same fiber is the image of that representative under an
   element of `pgg_G pgl27_M`. Derive pairwise reachability by composing one
   witness with the inverse of the other.
2. Use `pgl27_3transitive` and the cross-ratio classifier to prove transitivity
   on each fiber. This route is acceptable only if the unordered four-subset
   bookkeeping remains small and the final proof is axiom-free.

The first route is recommended because it matches the existing finite BFS
certificate used for `pgl27_3transitive`. Do not use a large unrestricted
computation over all of `S_8` if a certificate over the generated group or its
generator words is sufficient.

The formalization tool decides the proof body after a compilable probe. It must
not weaken the required theorem to fit a convenient proof.

## 6. Probe gate before implementation

Before writing an implementation plan, create and keep a probe file under the
project's scratch or probe convention. The probe must:

1. Import the same modules as `pgl27_orbit.v`.
2. State `subset_class_invariant` at the concrete carrier shown above.
3. State the full two-way `subset_class_orbit` result.
4. Exercise the exact set image notation and group membership types. A bare
   `Check` command is not enough.
5. Confirm that the two intended representatives have cardinality four and
   opposite classifier values.
6. Mutation-check the reachability claim by replacing equal classifier values
   with opposite values and confirming that the altered claim fails.
7. Record the probe path and build command in the implementation report.

Use the real project build with one worker:

```text
make -j1 <probe-target>.vo
```

Do not run concurrent Rocq compilations.

## 7. Soundness invariants

The finished work must satisfy all of these claims:

1. No new `Axiom`, `Parameter`, `Admitted`, or `Abort` is introduced.
2. The orbit witness belongs to `pgg_G pgl27_M`. Membership in the full
   symmetric group is not enough.
3. Both subsets are explicitly restricted to cardinality four.
4. The theorem proves that each Boolean fiber is one orbit. It does not infer
   this from invariance and the numbers 28 and 42 alone.
5. The theorem uses the same action orientation as the existing subset image
   notation. If the implementation chooses `S = g @: T` instead of
   `T = g @: S`, it must provide the stated orientation as a corollary.
6. No probability, privacy, recovery, or mixing theorem is changed.
7. No identification theorem between the concrete generated group and the
   abstract quotient `pgl2 'F_7` is required by this request.
8. The final declaration comments contain only short mathematical statements.
   Proof strategy and implementation status stay outside rendered statement
   comments.

There are no distributional claims, adversary parameters, or asymptotic bounds
in this request. The usual average-case and vacuity conditions for security
statements therefore do not apply.

## 8. Claim ledger

| Claim | Current evidence | Passing condition |
|---|---|---|
| The classifier is invariant on subsets. | Local `stabpP` and `G_sub_stabp`. | A public compiled lemma with the statement in Section 3.1. |
| The true fiber is one orbit. | Not formalized. | A compiled reachability proof for all cardinality-four subsets in the true fiber. |
| The false fiber is one orbit. | Not formalized. | A compiled reachability proof for all cardinality-four subsets in the false fiber. |
| Equal class is equivalent to the same orbit. | Not formalized. | Public `subset_class_orbit` or an exact equivalent corollary. |
| The two orbit sizes are 28 and 42. | Existing count lemmas. | The new orbit theorem composes with both existing count lemmas without an informal step. |

## 9. Non-goals

Do not perform any of the following work:

- Do not edit the WADT paper or its bibliography.
- Do not alter the protocol, encoder, privacy theorem, recovery theorem, or
  finite-step mixing section.
- Do not build a general cross-ratio library for arbitrary finite fields.
- Do not formalize an isomorphism between the generated shuffle group and
  `pgl2 'F_7`.
- Do not rename existing public declarations unless a collision makes it
  necessary.
- Do not replace existing proofs merely for style.

## 10. Verification and completion report

The formalization is complete only when all of the following checks pass:

1. `make -j1 pgg-smc/instances/pgl27/pgl27_orbit.vo`
2. No `Admitted`, `admit`, `Abort`, new axiom, or new assumed constant in the
   touched scope.
3. `Print Assumptions` on `subset_class_invariant` and
   `subset_class_orbit`, with no new custom assumptions.
4. The Rocq audit gate passes for the touched `.v` files without `--no-verify`.
5. A soundness reviewer confirms that the forward implication proves
   transitivity on each fiber.
6. A naming reviewer confirms the final public identifiers and their statement
   comments follow the project rules.

The completion report must list:

- every modified file
- the final theorem names and exact statements
- the proof route used
- the probe path
- the build command and result
- the `Print Assumptions` result
- any difference from this request

The formalization tool must not edit `pgg-smc/paper-wadt2026/main.tex`. The paper
writer will add the theorem-title footnote after the new Rocq declarations are
available.
