# Rocq formalization request: unified analysis pipelines for all protocol instances

Date: 2026-08-12.

Request path:
`docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-request.md`

Expected response path:
`docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-response.md`

Status: REQUEST ONLY. This document does not authorize edits to the WADT paper.
The formalization tool must evaluate the design, run the required probes, and
return a GO or NO-GO verdict before it writes an implementation plan. It may
implement a phase only after its probes return GO.

This request follows the completed layered-packing work at commit `88ed16a2`.
It extends Phase H2 of
`2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`. It does not
reopen the record migration, PGL facade, five-card facade, or the five existing
manifest rows unless a required new alias exposes a real defect in them.

## 1. Goal

Give every live protocol instance the same level of analysis coverage and the
same public route through the formalization.

The live protocol instances in scope are:

1. PGL27
2. the five-card family, with den Boer and Kim as separate analysis paths
3. S5
4. S5xS5
5. Abelian

PGL27 and the five-card family already supply the reference shape. This request
must bring S5, S5xS5, and Abelian to that shape.

Every completed instance must expose this chain:

```text
Program
  -> Execution
  -> Observers
  -> Models
  -> Correctness
  -> Security analysis
  -> Transfer
  -> Facade and manifest rows
```

The same shape does not mean the same theorem. S5 and S5xS5 should end in
positive secrecy or quantitative results. Abelian should end in a formal
negative result. Its negative result must show an observable limitation of its
actual execution or shuffle model.

The completed work must support this statement:

> Every protocol instance has one typed public analysis route. The route joins
> its shared program, actual interpreter execution, named observers, probability
> models, correctness theorem, and strongest proved security or failure result.

It must not imply this statement:

> Every protocol instance satisfies the same security property.

## 2. Paper scope and repository scope

The WADT paper still uses only these featured protocol instances:

- PGL27
- den Boer and Kim as models of the five-card family

S5, S5xS5, and Abelian are repository-level completeness work. This request
does not require adding them to the paper narrative.

The following developments are out of scope because they do not currently
provide a live `MonodromyProfile`:

- OC
- Monster
- Cyclic
- Star

They may remain group-theory, rigidity, or exploratory artifacts. Do not add
dummy profiles merely to make the manifest look exhaustive.

## 3. Meaning of equal comprehensiveness

Equal comprehensiveness is measured by connected layers, not by file count,
theorem count, or identical theorem statements.

An instance is complete only when it has at least one analysis path with all of
the following typed witnesses:

| Layer | Required witness |
|---|---|
| Program | one probability-independent `MonodromyProfile` |
| Execution | one `ExecutionPlug` using the actual piSMC process flow |
| Observers | one `ObservedExecution` and named executed observers |
| Models | at least one `SampleAdapter` with named distributions |
| Correctness | termination, endpoint count, and recovery for the packaged run |
| Security analysis | a positive secrecy, privacy, leakage, or negative limitation theorem about a named model and observer |
| Transfer | a theorem connecting static and executed observations, plus a model-transfer theorem when the path compares ideal and finite shuffles |
| Public API | a seven-section facade and checked manifest rows |

The security layer may contain several theorem capabilities. Do not collapse
them into a Boolean `secure` field.

Every path must also report its transfer status. A path that compares ideal and
finite models needs a typed model-transfer theorem. A path that does not make
that comparison may report no model-transfer capability, but it must name the
missing mathematical premise. Five-card is the current example: its facade has
executed security bridges, but no ideal-to-finite theorem because the required
ideal distribution equality has not been established. An absent transfer
capability must not raise or lower an unrelated security claim.

An instance is not complete when it has only:

- a `MonodromyProfile`
- a set of interpreter lemmas outside `ExecutionPlug`
- static security theorems not connected to an executed observer
- a facade with empty sections
- a prose manifest row without typed witnesses

For Abelian, equal comprehensiveness means a complete analysis with a negative
conclusion. It does not mean manufacturing a positive privacy theorem.

## 4. Current baseline

### 4.1 Completed reference instances

These files define the reference public shape:

- `pgg-smc/instances/pgl27/pgl27_analysis.v`
- `pgg-smc/instances/kim2025/five_card_analysis.v`
- `pgg-smc/manifest/pgg_analysis_manifest.v`
- `pgg-smc/manifest/pgg_analysis_client.v`

Both facades use this order:

1. Program
2. Execution
3. Observers
4. Models
5. Correctness
6. Security
7. Transfer

The new facades must use the same order. This order is a source and navigation
contract. It is not a large dependent record.

The five-card Transfer section is intentionally empty in the baseline. This
does not make the five-card security bridges incomplete. It records that no
ideal-to-finite comparison has been proved for those models. This request does
not manufacture such a theorem merely for symmetry.

### 4.2 S5 already has substantial facts

The evaluator must preserve and reuse at least these sources:

- `pgg-smc/instances/s5/s5_profile.v`
- `pgg-smc/instances/s5/s5_run.v`
- `pgg-smc/instances/s5/s5_trace.v`
- `pgg-smc/instances/s5/s5_secrecy.v`
- `pgg-smc/instances/s5/s5_mixing.v`
- `pgg-smc/instances/s5/rigidity_s5_instance.v`

The baseline includes:

- `s5_profile`
- `s5_run_terminates`
- `s5_endpoints`
- `s5_endpoints_size`
- `s5_run_recovers`
- `s5_trace_secrecy`
- `s5_view_secrecy_concrete`
- `s5_spectral_convergence_proved`
- `s5_spectral_convergence_gap`

S5 is therefore not merely Algebraic. Its problem is that these facts have not
been connected to `ExecutionPlug`, `ObservedExecution`, `SampleAdapter`, and a
public facade.

### 4.3 S5xS5 already has substantial facts

The evaluator must preserve and reuse at least these sources:

- `pgg-smc/instances/s5x5/s5x5_profile.v`
- `pgg-smc/instances/s5x5/s5x5_run.v`
- `pgg-smc/instances/s5x5/s5x5_trace.v`
- `pgg-smc/instances/s5x5/s5x5_secrecy.v`
- `pgg-smc/instances/s5x5/s5x5_mixing.v`
- `pgg-smc/instances/s5x5/rigidity_s5x5_instance.v`

The baseline includes:

- `s5x5_profile`
- `s5x5_run_terminates`
- `s5x5_endpoints`
- `s5x5_endpoints_size`
- `s5x5_run_recovers`
- `s5x5_trace_secrecy`
- `s5x5_view_secrecy_concrete`
- `s5x5_joint_view_secrecy`
- `s5x5_pile1_TV_bound`
- `s5x5_pile2_TV_bound`
- `s5x5_spectral_TV_bound`

S5xS5 has the same packaging gap as S5. Its two-pile structure must remain
visible in the new observers and theorem statements.

### 4.4 Abelian has a profile and algebraic limitations

The evaluator must preserve and reuse at least these sources:

- `pgg-smc/instances/abelian/abel_profile.v`
- `pgg-smc/instances/abelian/abelian_word_collapse.v`
- `pgg-smc/instances/abelian/rigidity_abelian_instance.v`
- `pgg-smc/instances/abelian/pgg_abelian.v`

The baseline includes:

- `abel_profile`
- `profile_k_abel`
- `abel_gens_commute`
- `abelian_word_eval`
- `freq_vec_det`
- `abelian_search_space_bound`
- `abel_security_witness_direct_1`

These facts do not yet prove an executed security failure. In particular,
commuting generators alone do not imply privacy failure. A `ShuffleMarginalBound`
at one word length is also not a protocol privacy theorem.

The Abelian phase must first choose and compile a precise negative target.

## 5. Architectural invariants

### 5.1 Keep the landed package boundaries

The new work must use the existing chain:

```text
MonodromyProfile
  -> ExecutionPlug
  -> ObservedExecution
  -> SampleAdapter
```

Do not move probability fields back into `MonodromyProfile`. Do not add a
record that stores every theorem about an instance.

### 5.2 Use actual interpreter executions

S5, S5xS5, and Abelian must use the same piSMC execution mechanism as the
featured instances. A new package may reuse an existing process list or define
the missing one. It must not replace interpreter execution with a static model
solely to make the package easy to construct.

### 5.3 Preserve observer types

The common template fixes the role of an observer, not its carrier.

- S5 may use seat, coalition, content-trace, and verifier observers.
- S5xS5 must preserve pile membership and joint observations.
- Abelian must expose the observer used by its negative theorem.

Do not erase these differences with one untyped list or one generic Boolean
reader.

### 5.4 Keep raw traces outside finite distributions

Raw interpreter traces have sequence carriers. Do not construct an `fdist` over
an unconstrained raw trace. Define a finite reader and prove its relation to the
raw trace before using it in `SampleAdapter` or information theory.

### 5.5 Keep correctness and security separate

Termination and recovery do not prove privacy. Mixing of one endpoint does not
prove coalition privacy. A static secrecy theorem does not become an executed
secrecy theorem until an explicit observation equality connects them.

### 5.6 Use thin facades

Facades may alias existing values and theorems. They must not copy proof bodies
or restate weaker versions merely to achieve uniform naming.

## 6. Required Phase 0: inventory and compiled probes

Phase 0 is a hard gate. It must produce a response before any permanent
implementation begins.

### 6.1 Baseline build

Run a serial build from the correct opam environment. Use `make -j1` only.
Record the exact command, Rocq version, OCaml version, exit status, and elapsed
time.

At minimum, force or otherwise verify the dependency cone for:

- `pgg_analysis_client.vo`
- `s5_run.vo`
- `s5x5_run.vo`
- `abel_profile.vo`
- `abelian_word_collapse.vo`

Do not delete broad build directories. If a force rebuild is needed, remove
only the exact `.vo` target and document it.

### 6.2 Live declaration inventory

For S5, S5xS5, and Abelian, report:

- profile and reconstruction plug
- current process list and fuel
- termination and endpoint equations
- recovery theorem
- raw and finite observers
- sample spaces and distributions
- static secrecy or mixing theorems
- exact and finite-word bounds
- assumptions of every candidate public theorem
- all current consumers of declarations that must be wrapped or renamed

Correct the earlier H2 description that called S5 and S5xS5 Algebraic only.
They have actual run and recovery lemmas, but no landed `ExecutionPlug` package.

### 6.3 ExecutionPlug probes

Create permanent probe files or MCP-checked snippets for:

- an S5 `ExecutionPlug` built from the existing run
- an S5xS5 `ExecutionPlug` built from the existing run
- an Abelian process list and `ExecutionPlug`

Each probe must establish that the chosen players, fuel, process list,
termination fact, endpoint count, and reconstruction equation have the exact
types required by `ExecutionPlug`.

If an existing run cannot be definitionally reused, report the smallest bridge
needed. Do not duplicate the process definition before proving that a bridge is
impossible.

### 6.4 ObservedExecution probes

For each instance, probe one `ObservedExecution` value. Report its:

- input carrier
- shuffle argument carrier
- static observation
- executed endpoint observation
- recovery value
- hypotheses

Probe the exact equalities that will connect static readers to executed finite
readers. Merely defining both readers is not enough.

### 6.5 SampleAdapter probes

For every proposed analysis path, compile a provisional `SampleAdapter` and its
distribution equations.

At minimum, probe:

- S5 ideal model
- S5 finite-word model
- S5xS5 ideal model
- S5xS5 finite-word model
- Abelian ideal target model
- Abelian actual finite-word model

Each probe must identify:

- sample carrier
- prior distribution
- map into the interpreter input and shuffle argument
- finite executed reader
- cut distribution
- executed observer distribution

Do not infer the appropriate prior from the profile. Probability remains a
separate layer.

### 6.6 Positive bridge probes

For S5 and S5xS5, compile the proposed bridges from existing static theorems to
executed observers.

The probes must answer:

- whether the existing trace theorem uses the same distribution as the new
  adapter
- whether the existing coalition view has the same carrier and indexing as the
  executed reader
- whether the mixing theorem bounds the same shuffle distribution used by the
  finite-word adapter
- whether the generic transfer theorem applies with no changed constants

Any mismatch must be stated as a new proof obligation. Do not hide it with a
cast or a renamed alias.

### 6.7 Abelian negative-result probe

The evaluator must select one primary negative statement and compile its exact
carrier and quantifiers before implementation. Preferred candidates are:

1. a fixed-word shuffle distribution remains a positive full-L1 distance from
   its stated ideal group distribution for all relevant word lengths
2. an algebraic orbit or parity invariant is visible through a finite executed
   observer
3. two secrets induce executed view distributions with a positive full-L1
   distance
4. a named information-leakage quantity has a positive lower bound

Candidate 1 or 2 is sufficient for a complete negative shuffle analysis.
Candidate 3 or 4 is stronger and may be used only if the current definitions
support it.

The selected statement must satisfy all of these conditions:

- its ideal distribution is named and mathematically justified
- its actual distribution is the one used by the Abelian `SampleAdapter`
- its observer is finite and connected to the interpreter execution
- its lower bound is explicit and nonzero
- the proof does not infer the result from commutativity alone
- the theorem is labelled as a mixing, anonymity, or privacy limitation
  according to its actual statement

If no candidate compiles or is mathematically true, return NO-GO for Phase 3.
Do not replace it with a vague theorem about search-space size.

### 6.8 Facade and manifest probe

Probe the final import graph for:

- `s5_analysis.v`
- `s5x5_analysis.v`
- `abelian_analysis.v`
- the updated repository manifest
- the clean one-import client

The probe must show that no import cycle is introduced and every proposed alias
can be checked from the manifest import.

### 6.9 Phase 0 report

Return one verdict per instance:

- S5 GO or NO-GO
- S5xS5 GO or NO-GO
- Abelian GO or NO-GO

A NO-GO for one instance does not block a GO instance. The report must give the
exact failed statement, type error, missing theorem, or false mathematical
claim. General estimates such as "too difficult" are not enough.

## 7. Required Phase 1: S5 complete analysis path

Phase 1 begins only after the S5 probes return GO.

### 7.1 Program

Keep `s5_profile` as the probability-independent profile. Preserve
`profile_k_s5`. Do not create separate profiles for ideal and finite shuffles.

### 7.2 Execution

Construct an `ExecutionPlug s5_profile` from the current S5 run. Reuse:

- `s5_players`
- `s5_procs`
- fuel 150, unless the probe proves another existing constant is authoritative
- `s5_run_terminates`
- `s5_endpoints`
- `s5_endpoints_size`
- `s5_run_recovers`

If concrete player lists are retained for reduction speed, add a comment that
states their computational role. Do not replace them with `enum` without a
timed reduction probe.

### 7.3 Observers

Construct an S5 `ObservedExecution`. Expose at least:

- one seat endpoint
- one coalition endpoint view
- one finite content-trace reader that matches the existing secrecy theorem
- verifier endpoints
- raw trace extractors for navigation only

Prove the finite reader equalities required to identify existing static views
with executed observations.

### 7.4 Models

Construct at least two S5 sample paths:

1. an ideal model used by the existing exact secrecy statement
2. a finite-word model using the distribution bounded by the landed mixing
   theorem

If the existing secrecy result and ideal model use a randomized-sharing space
rather than a group-uniform sample space, keep that distinction explicit. Do
not call two definitionally different priors equal without a theorem.

Expose all cut, seat, coalition, trace, and joint distribution equations needed
by the final security and transfer theorems.

### 7.5 Correctness

Transport the current termination, endpoint-count, and recovery facts through
the package. The facade must expose both the bundled correctness result and the
recovery theorem.

### 7.6 Security

Bridge the strongest existing S5 results that match the new adapters and
executed readers. At minimum, include:

- executed single-seat trace secrecy
- executed coalition view secrecy below the proved threshold
- the applicable quantitative finite-word mixing bound

Do not describe endpoint mixing as coalition privacy. If a full finite-word
coalition privacy theorem needs an additional data-processing argument, state
and prove that bridge or report it as a separate missing result.

### 7.7 Transfer

Specialize the generic ideal-to-finite transfer theorem when its hypotheses
match the S5 models. The final statement must name:

- ideal distribution
- finite-word distribution
- executed observer
- security notion
- full-L1 convention
- exact bound with no silent factor change

If only a static-to-executed transfer is currently possible, the phase remains
incomplete until the response either proves the model transfer or gives a
formal non-applicability result accepted by a revised request.

### 7.8 Public API

Add an S5 facade with the seven fixed sections. Add one manifest row per S5
analysis path. Every row must name the exact observer and theorem capability.

## 8. Required Phase 2: S5xS5 complete analysis path

Phase 2 begins only after the S5xS5 probes return GO.

### 8.1 Program and execution

Keep `s5x5_profile`. Construct an `ExecutionPlug` from the existing run. Reuse:

- `s5x5_players`
- `s5x5_procs`
- the existing fuel
- `s5x5_run_terminates`
- `s5x5_endpoints`
- `s5x5_endpoints_size`
- `s5x5_run_recovers`

Do not flatten the two piles in the public statements merely to reuse S5 names.

### 8.2 Observers

Construct one `ObservedExecution` and expose at least:

- a pile-one seat observer
- a pile-two seat observer
- a pile-one coalition observer
- a pile-two coalition observer
- a joint coalition observer
- finite trace readers used by the landed secrecy results
- verifier endpoints

The types must retain pile membership, coalition bounds, and joint structure.

### 8.3 Models

Construct ideal and finite-word sample paths that match the landed S5xS5
secrecy and mixing theorems. Expose separate pile distributions and the joint
distribution when a joint theorem uses it.

Do not infer joint independence from two marginal bounds. A joint theorem needs
the exact product or coupling fact required by its statement.

### 8.4 Correctness

Transport termination, endpoint count, and joint recovery through the package.

### 8.5 Security

Bridge at least:

- executed pile-one secrecy
- executed pile-two secrecy
- executed joint view secrecy under the proved coalition constraints
- pile-one and pile-two finite-word mixing bounds
- the strongest valid joint finite-word bound

Preserve the distinction among `s5x5_pile1_TV_bound`,
`s5x5_pile2_TV_bound`, and `s5x5_spectral_TV_bound`.

### 8.6 Transfer

Provide static-to-executed bridges and every valid ideal-to-finite
specialization. State all per-pile and joint assumptions. Do not lift two
separate transfer bounds to a joint security claim without a proved theorem.

### 8.7 Public API

Add an S5xS5 facade with the seven fixed sections. Add one manifest row per
analysis path. The rows must make per-pile and joint capabilities distinct.

## 9. Required Phase 3: Abelian complete negative analysis

Phase 3 begins only after one Abelian negative target returns GO.

### 9.1 Program

Keep `abel_profile` and `profile_k_abel`. Do not interpret the threshold value
as a security proof.

### 9.2 Execution

Define or connect an Abelian piSMC run using the shared program flow. Construct
an `ExecutionPlug abel_profile` with explicit players, fuel, termination,
endpoint count, and reconstruction facts.

The execution must use the actual Abelian generators and reconstruction plug.
It must not reuse S5 execution under an unproved cast.

### 9.3 Observers

Construct one `ObservedExecution`. Expose:

- seat endpoints
- the smallest finite joint endpoint observer needed by the negative theorem
- verifier endpoints
- a finite content reader when it is used by a secrecy or leakage statement
- raw traces for navigation only

The selected negative observer must be executable and must expose the algebraic
invariant used in the proof.

### 9.4 Models

Construct at least:

1. the mathematically justified ideal target model
2. the actual finite-word Abelian shuffle model

Name the word distribution, length parameter, parity or frequency data, and
the executed observation distribution. Use the same probability convention as
the theorem statement.

### 9.5 Correctness

Prove termination, endpoint count, and recovery. The protocol may be correct
while its shuffle security goal fails. The facade must expose both facts
without contradiction.

### 9.6 Negative security or mixing result

Prove the Phase 0 selected statement. The result must end at a named executed
observer.

The preferred proof chain is:

```text
commuting or orbit structure
  -> word evaluation invariant
  -> support or distinguishability fact for the actual sample model
  -> finite static observation limitation
  -> executed observation equality
  -> explicit nonzero distance or leakage lower bound
```

`abel_gens_commute`, `abelian_word_eval`, `freq_vec_det`, and
`abelian_search_space_bound` may support the proof. None of them alone is the
final negative result.

Do not call the theorem privacy failure when it proves only failure to mix to a
chosen ideal distribution. Use the narrowest accurate capability label.

### 9.7 Transfer

The Abelian transfer section must connect the algebraic invariant to the
executed negative conclusion. It need not state a positive ideal-to-finite
security theorem.

If the negative result is a persistent distance from an ideal model, expose the
static and executed forms and their equality. If it is a privacy or leakage
lower bound, expose the exact observer and secret distributions.

### 9.8 Public API

Add an Abelian facade with the seven fixed sections. Add manifest rows for its
ideal and actual paths. Label the actual capability as a precise limitation,
not as `secure` and not as an unqualified failure.

## 10. Required Phase 4: repository-wide public contract

Phase 4 runs after every GO implementation phase.

### 10.1 Facade order

Every protocol facade must use:

1. Program
2. Execution
3. Observers
4. Models
5. Correctness
6. Security
7. Transfer

PGL27 and five-card may keep their current public names unless the manifest
checker exposes a real inconsistency.

### 10.2 Manifest rows

Update `pgg_analysis_manifest.v` with one row per implemented analysis path.
Each row must name:

- protocol instance
- probability model
- profile alias
- execution alias
- observed-execution alias
- sample alias
- observer alias and carrier
- correctness theorem
- security, leakage, mixing, or limitation theorem
- static-to-executed bridge, plus a model-transfer theorem when present
- missing model-transfer premise when no model-transfer theorem is claimed
- exact theorem capability
- completion level

Do not place completion levels only in comments. Extend the checker so that
required aliases and their exact types are compiled. If a fully typed manifest
record is not feasible, report that limitation and retain a compile-checked
navigation table. Do not claim it is a kernel-level registry.

### 10.3 Clean client

Update the one-import client so it reaches one representative alias from every
section of every implemented facade. Keep instance namespaces distinct.

### 10.4 Completeness check

Add a reproducible check that finds every live `MonodromyProfile` constructor
or alias and classifies it as:

- represented by a complete facade
- a deliberate alias of another represented profile
- out of scope with an exact reason

Expected classifications are:

- PGL27: represented
- five-card: represented
- den Boer: deliberate five-card alias with separate model rows
- S5: represented after Phase 1
- S5xS5: represented after Phase 2
- Abelian: represented after Phase 3

The check must not treat names in comments as constructors.

## 11. Commenting requirements

Follow the repository comment audit for every touched Rocq declaration.

Comments must describe mathematical or computational meaning. They must not
contain progress narration, proof estimates, or claims of importance.

Add precise comments for retained fields or concrete data whose role is not
obvious:

- concrete player lists retained as reduction caches
- fuel values retained because termination facts are computed at that fuel
- endpoint readers and their carrier
- raw trace extractors that are not finite random variables
- per-pile indices in S5xS5
- the ideal target chosen for the Abelian negative theorem
- the full-L1 convention of every variation-distance lower or upper bound

The facade comments must state when a result is:

- correctness
- exact privacy
- approximate privacy
- trace secrecy
- conditional entropy
- mutual information
- endpoint marginal mixing
- negative mixing result
- anonymity or privacy limitation

Do not use a broader label than the theorem statement supports.

## 12. Soundness requirements

1. Add no `Axiom`, `Parameter`, `Admitted`, or `Abort` to permanent sources.
2. Do not change an existing theorem statement merely to fit a package.
3. Preserve every hypothesis, carrier, index domain, and numeric bound.
4. Keep all variation-distance factors consistent with the repository's
   full-L1 convention.
5. Do not infer joint secrecy from marginal secrecy.
6. Do not infer coalition privacy from one-seat endpoint mixing.
7. Do not infer privacy failure from commutativity alone.
8. Do not infer protocol failure from a search-space upper bound alone.
9. Do not define a finite distribution over an unconstrained raw trace.
10. Do not replace the actual piSMC run with a static surrogate.
11. Do not duplicate proof bodies in facades.
12. Do not introduce a large record containing optional theorem proofs.
13. Do not move probability or word-length data into `MonodromyProfile`.
14. Do not flatten S5xS5 pile structure.
15. Do not claim a kernel-level typed registry when the manifest level remains
    a checked source table.
16. Use `make -j1` for all builds.
17. Run the repository Rocq audit on every touched `.v` file before commit.
18. Run `Print Assumptions` on every new public theorem.
19. Do not edit the paper, slides, bibliography, or the completed layered
    packing response in this task.

## 13. Phase acceptance conditions

### 13.1 S5

S5 passes only if:

- its existing run is represented by `ExecutionPlug`
- `ObservedExecution` compiles
- ideal and finite sample adapters compile
- correctness is transported
- at least one positive secrecy theorem reaches an executed observer
- the finite model has its exact valid transfer or a separately approved
  formal non-applicability result
- its facade and manifest rows compile from the clean client

### 13.2 S5xS5

S5xS5 passes only if:

- its existing run is represented by `ExecutionPlug`
- `ObservedExecution` compiles
- pile and joint observers retain their types
- ideal and finite sample adapters compile
- joint recovery is transported
- the existing positive secrecy results reach executed observers
- marginal and joint transfer claims remain distinct
- its facade and manifest rows compile from the clean client

### 13.3 Abelian

Abelian passes only if:

- it has an actual piSMC `ExecutionPlug`
- `ObservedExecution` compiles
- ideal and actual sample adapters compile
- termination and recovery are proved
- one explicit nonzero lower bound or equivalent limitation theorem reaches a
  finite executed observer
- the theorem is labelled according to its exact security or mixing meaning
- its facade and manifest rows compile from the clean client

### 13.4 Repository

The repository passes only if every in-scope profile is represented by a
complete facade or a documented alias of one. An empty section does not satisfy
a required layer merely by existing. A path may still report no
ideal-to-finite capability under the transfer-status rule in Section 3.

## 14. Verification

For each phase, run and report:

1. focused serial builds for every touched `.vo`
2. the clean one-import client build
3. a serial build of the full affected dependency cone
4. repository audits for touched `.v` files
5. an `Admitted` and `Abort` scan over touched files
6. `Print Assumptions` for every new public theorem
7. manifest mutation checks that demonstrate failure when a required alias is
   removed or given an incompatible type
8. timed reduction checks when changing a concrete player list or fuel path

The final build report must distinguish new warnings from existing warnings.

## 15. Required completion report

The response document must include:

1. GO or NO-GO for Phase 0 and for each instance
2. the exact baseline commit and final commit
3. the exact declarations reused from each instance
4. the final package values and their types
5. one table of all observers and carriers
6. one table of all sample models and distributions
7. one table of correctness, security, mixing, limitation, and transfer
   theorems
8. every new bridge and both endpoints it connects
9. the selected Abelian negative theorem and why its label is accurate
10. any stronger Abelian privacy or leakage claim that remains unproved
11. every missing layer after implementation
12. final facade paths and seven-section inventories
13. all manifest rows and their completion levels
14. evidence from the clean one-import client
15. build commands, timings, exit statuses, and warning counts
16. audit commands and outcomes
17. `Print Assumptions` results
18. changed files and commits by phase
19. the strongest repository-facing claim now supported
20. nearby claims that remain false

## 16. Non-goals

This request does not ask for:

- changes to the WADT paper
- adding S5, S5xS5, or Abelian to the paper narrative
- identical security theorem statements for all instances
- automatic security from `MonodromyProfile`
- active, compositional, or post-reveal security
- new profiles for OC, Monster, Cyclic, or Star
- a redesign of `ReconPlug`, `PGGInterface`, or the interpreter
- a record that stores every theorem about an instance
- a positive Abelian privacy theorem
- calling an Abelian mixing limitation a privacy failure without a matching
  privacy statement
- changing PGL27 or five-card mathematics solely for naming symmetry

## 17. Final acceptance statement

The entire request is complete only when the formalization supports this
statement:

> PGL27, the five-card family, S5, S5xS5, and Abelian each have a typed public
> route from program profile to actual piSMC execution, finite observations,
> probability models, correctness, and their strongest justified positive or
> negative analysis. Each path states its exact transfer status. Their facades
> use one navigation template while preserving different observer types and
> theorem meanings.

It must also make this limitation explicit:

> A common analysis template organizes evidence. It does not make different
> protocols satisfy the same security theorem, and it does not make security an
> automatic consequence of filling `MonodromyProfile`.
