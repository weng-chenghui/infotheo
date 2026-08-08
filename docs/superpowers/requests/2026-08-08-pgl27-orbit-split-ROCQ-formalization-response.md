# Response: PGL(2,7) four-subset orbit split

Date: 2026-08-08

Paired with: `docs/superpowers/requests/2026-08-08-pgl27-orbit-split-ROCQ-formalization-spec.md`

Status: DONE. All required results are compiled and axiom-free.

## 1. What was done

The request asked to close one gap. The development already knew that the
classifier `subset_class` is invariant under the shuffle group, and that its two
Boolean fibers contain 28 and 42 four-subsets. It did not know that either fiber
is a single orbit. A fiber could have been several smaller orbits that happen to
add up to the right number.

That gap is now closed. Three new public results in
`pgg-smc/instances/pgl27/pgl27_orbit.v`:

| Name | What it says |
|---|---|
| `subset_class_invariant` | Shuffling a four-subset does not change its class. |
| `subset_class_orbit` | Two four-subsets have the same class exactly when one is a shuffle image of the other. Both directions. |
| `subset_class_orbitE` | The orbit of a four-subset is exactly the class fiber it sits in. |

`subset_class_orbitE` is one result beyond the requested list. It states "each
fiber is one orbit" directly, instead of leaving a reader to assemble it, and it
composes with the existing count lemmas to give the paper sentence with no
informal step.

Nothing else changed. `pgl27_group.v` was not touched, no existing proof was
rewritten, no statement was weakened, and no probability, privacy, recovery or
mixing result was touched.

## 2. Commits

| Hash | Branch | Contents |
|---|---|---|
| `d18003c` | `pgg-smc` | The formalization. 202 added lines in `pgl27_orbit.v`, plus the probe files and the request document. |
| `42b8a99` | `pgg-smc` | Style-audit fixes on the new block. Statements unchanged. |

Both passed the pre-commit audit gate without `--no-verify` and without a bypass.

Verification results:

- `make -j1 pgg-smc/instances/pgl27/pgl27_orbit.vo` passes in about 6 seconds.
- The six downstream `pgl27` files rebuild clean in about 51 seconds.
- `Print Assumptions` on all three results reports "Closed under the global
  context", so there are no axioms at all, not even the classical ones.
- No `Admitted`, no `Abort`, no new axiom, no line over 80 columns.

Probe files are kept at
`docs/superpowers/probes/2026-08-08-pgl27-orbit-split/`, with the build command
in `rebuild.sh`.

## 3. Strategies used

1. **Probe before planning.** Wrote throwaway Rocq files to test the risky
   claims first, and only then wrote code meant to stay. The spec asked for this
   and it paid: the whole design was validated before a single line landed in the
   real file.

2. **Split the probe by risk, not by topic.** The one claim nobody had ever run
   was "a search over four-subsets terminates and covers a whole fiber". That
   went into a standalone file with no heavy imports, so it compiled in 4 seconds
   instead of 7. The interface questions went into a separate probe built on a
   copy of the real file.

3. **Reused the existing certificate idea rather than building a theory.** The
   file `pgl27_group.v` already proves 3-transitivity by searching for generator
   words over ordered triples. The same search was lifted from triples to
   unordered four-element subsets. No new geometry was formalized.

4. **Gave each subset a canonical form.** Every subset reached by the search is
   stored as its sorted list of card codes. That makes two subsets comparable by
   plain equality, which is what lets the search deduplicate and lets the final
   check be a single computation.

5. **Made the certificate check itself.** The checker does not trust the search.
   For every four-subset of the right class it recomputes the recorded word from
   the representative and confirms the result. A bug in the search can only make
   the check fail, never make it wrongly pass.

6. **Tried to break the claim on purpose.** Swapped the classifier value and
   confirmed the reachability check turns false. Then proved, in Rocq, that the
   two representatives are *not* shuffle-related. So the theorem is about two
   genuinely different orbits, and the forward direction is not vacuous.

7. **Kept every new helper local to one file.** Exporting the word machinery
   from `pgl27_group.v` would have been tidier on paper, but that file is a
   dependency of seven others including the slow mixing file. Rebuilding all of
   them buys nothing mathematically, so the machinery was rebuilt locally in
   about 50 lines.

8. **Read the goal instead of guessing at it.** Signatures and goal states came
   from the interactive Rocq tooling. Editing the file and recompiling to find out
   what the next error is was the wrong loop and was abandoned partway through.

9. **Golfed only after it was correct, and only proof bodies.** No statement,
   name, or statement comment was changed by golfing. Axioms were re-checked
   afterwards.

10. **Had a separate reviewer read the result, then checked the review.** A
    mathcomp style auditor produced 27 findings. Each substantive one was tested
    against the live goal before being applied. Two were rejected with evidence,
    including one that looked right and does not compile.

## 4. Open issues

1. **The audit gate's second stage never runs.** Every run emits
   `S998: --json-schema is not a valid JSON Schema: no schema with key or ref
   "https://json-schema.org/draft/2020-12/schema"`. This is only a warning, so
   the commit reports zero errors while the language-model review is silently
   skipped. A green gate currently means the regular expression checks passed and
   nothing more. This is pre-existing and unrelated to this work.

2. **No independent soundness reviewer ran.** Spec item 10.5 asks one to confirm
   that the forward implication really proves transitivity on each fiber. What
   exists instead is machine-checked evidence: the forward direction runs through
   a lemma quantified over every four-subset, and the non-reachability proof shows
   the two fibers are distinct. Spec item 10.6, the naming review, was covered by
   the style auditor.

3. **One duplicated proof was left in place.** The new `asc4_val_enum` is the
   same fact as a block already sitting inside the older `class_count`. Merging
   them would edit a pre-existing proof, which the request puts out of scope.

4. **The three new results have no caller yet.** That is expected. The intended
   consumer is the paper footnote, and the request explicitly reserves that for
   the paper writer.

5. **One deviation from the spec.** Section 6.7 asked for `make -j1 <probe>.vo`.
   The probes were compiled with `rocq compile` plus the project's include flags,
   one process at a time. Putting a probe in `_CoqProject` would have pulled it
   into the permanent build.

6. **A pre-existing naming warning remains.** `orbit_class_split_complement`
   trips the F001 name-grammar rule. It was already there and renaming it is
   forbidden by the request.

## 5. Candidates for further work

Roughly in order of value.

1. **Add the theorem-title footnote to the WADT paper.** This is the reason the
   work was requested. The three declarations are ready to cite, together with the
   two existing count lemmas.

2. **Fix the second-stage audit failure.** Until it is fixed, no commit in this
   repository is getting the semantic review the pipeline claims to give. This is
   the highest-value item that is not about this proof.

3. **Decide whether the "two distinct orbits" fact should be public.** It is
   currently proven only in a probe. If the paper wants to say the split is into
   two different orbits rather than merely two fibers of the right sizes, promote
   it into `pgl27_orbit.v`. It is a short proof.

4. **Merge the duplicated ascending-list lemma.** Small, safe, and needs a scope
   decision because it edits an existing proof.

5. **Reuse the pattern on other instances.** The recipe of canonical form, then
   word search, then a self-checking table is not specific to PGL(2,7). Any
   instance where a finite group acts on a small finite set and an orbit claim is
   wanted can use it. Worth considering before hand-rolling another orbit
   argument.
