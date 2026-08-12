# Rocq formalization request: unified analysis pipelines for all protocol instances

Date: 2026-08-12.

Request path:
`docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-request.md`

Expected response path:
`docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-response.md`

Status: REQUEST ONLY. Amended after two independent adversarial audits returned
NO-GO on the first revision. This document does not authorize edits to the WADT paper.
The formalization tool must evaluate the design, run the required probes, and
return a GO or NO-GO verdict before it writes an implementation plan. It may
implement a phase only after its probes return GO.

This request follows the completed layered-packing work at commit `88ed16a2`.
It replaces the implementation shape proposed for Phase H2 of
`2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`. It does not
reopen the record migration, PGL facade, five-card facade, or the five existing
security theorems. It may update the common manifest vocabulary, the clean
client, and transfer-status aliases when the repository-wide contract requires
it.

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

Every completed instance must expose this navigation chain:

```text
Program
  -> Execution
  -> Observers
  -> Models
  -> Correctness
  -> Security analysis
  -> Transfer status
  -> Facade and manifest rows
```

The same shape does not mean one execution plug or one theorem per instance.
S5 and S5xS5 already use a deterministic canonical encoding for correctness
and randomized layouts for secrecy. These are separate analysis paths over one
program profile. They must be packaged separately unless a proved execution
equivalence joins them. Abelian should end in a formal negative result. Its
negative result must show an observable limitation of its actual execution or
shuffle model.

The completed work must support this statement:

> Every protocol instance has one public facade. The facade exposes coherent
> typed analysis paths from its shared profile through actual interpreter
> executions, named observers, probability models, correctness, and the
> strongest justified security, mixing, or limitation results.

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

Equal comprehensiveness is measured at the instance facade, not by file count,
theorem count, or identical theorem statements. One facade may contain several
analysis paths. Every theorem must stay on one coherent path unless an explicit
bridge connects two paths.

An instance is complete only when its facade contains all of the following
typed evidence. The evidence may be split across a deterministic correctness
path, a randomized secrecy path, and a finite-word mixing path:

| Layer | Required witness |
|---|---|
| Program | one probability-independent `MonodromyProfile` |
| Execution | every claimed path has an `ExecutionPlug` using its actual piSMC process flow |
| Observers | every security or limitation path has an `ObservedExecution` and named executed observers |
| Models | every probabilistic path has a `SampleAdapter` with named distributions |
| Correctness | termination, endpoint count, and recovery for each execution whose result is used |
| Security analysis | the facade exposes a positive secrecy, privacy, leakage, or negative limitation theorem about a named model and executed observer |
| Transfer | every static theorem used by an executed claim has a static-to-executed bridge; ideal-to-finite transfer is required only when that comparison is claimed |
| Public API | a seven-section facade and checked manifest rows |

The security layer may contain several theorem capabilities. Do not collapse
them into a Boolean `secure` field.

Every path must report one typed transfer status from a new closed vocabulary:

```text
NoModelComparison
StaticExecutedOnly
IdealFinite
NegativeTransfer
```

`IdealFinite` requires a public model-transfer theorem. `NegativeTransfer`
requires a theorem that transports an algebraic or distributional obstruction
to an executed observer. The other two statuses carry no theorem proof, but the
manifest row must name the absent premise in its source table. Five-card uses
`StaticExecutedOnly`: its facade has executed security bridges, but no
ideal-to-finite theorem because the required ideal distribution equality has
not been established. An absent model-transfer capability must not raise or
lower an unrelated security claim.

The common cumulative completion vocabulary is:

```text
Algebraic
Executable
Observed
Sampled
AnalysisBridged
```

`AnalysisBridged` means that a named security, leakage, mixing, or limitation
theorem reaches the named executed observer. It replaces the older broad label
`Security-bridged`, which cannot accurately classify negative mixing paths.

An instance is not complete when it has only:

- a `MonodromyProfile`
- a set of interpreter lemmas outside `ExecutionPlug`
- static security theorems not connected to an executed observer
- a facade whose required evidence is absent
- a prose manifest row without typed witnesses

An empty Transfer section is allowed only when the facade exposes a
`NoModelComparison` or `StaticExecutedOnly` status alias. The clean client checks
that alias instead of inventing a theorem.

For Abelian, equal comprehensiveness means a complete analysis with a negative
mixing conclusion at an executed observer. It does not mean manufacturing a
positive privacy theorem.

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
does not make the five-card security bridges incomplete. Phase 4 adds only a
typed `StaticExecutedOnly` status alias and its client check. It does not
manufacture an ideal-to-finite theorem merely for symmetry.

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

The facts also belong to two different execution paths:

- `s5_procs s w0` uses the deterministic canonical encoding
  `ts_encode s5_scheme s` and supports the current termination and recovery
  theorems.
- `s5_rprocs u` uses a randomized-sharing tape and supports
  `s5_trace_secrecy`.

The new work must not alias the second path's theorem onto the first path.

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

It also has two execution paths. `s5x5_procs s w0` uses the deterministic
canonical encoding on `'I_10`. `s5x5_rprocs uv` uses two randomized-sharing
tapes whose secret carrier is a product. The static joint secrecy theorem does
not mention the interpreter. These paths require separate packages and new
reader bridges.

### 4.4 Trusted spectral certificate boundary

`s5_spectral_convergence_proved` and the S5xS5 spectral chain depend on the
existing `s5_rayleigh_Q2_R` axiom in `s5_mixing.v`. The project retains this
single axiom because expanding and checking the rational sum-of-squares
certificate in the Rocq kernel is not computationally practical in the current
environment.

This request does not ask to eliminate that axiom. It treats it as a named
trusted analytical certificate boundary. Every facade capability and manifest
row that depends on it must report `s5_rayleigh_Q2_R` in its assumption status.
The word `conditional` must appear in the source-table capability description.
This accepted trust boundary does not lower the instance's structural
completion level.

The existing rigidity developments also contain group-order and geometric
realisation assumptions. This request does not remove them. It must report them
whenever they occur in `Print Assumptions` for a public value or theorem. The
kernel-efficiency justification in this section applies only to
`s5_rayleigh_Q2_R`. No new axiom is permitted.

### 4.5 Abelian has an incoherent execution interface and algebraic limitations

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

The current `abel_profile` cannot construct an `ExecutionPlug`.
`Gen_PGG_2 abel_sigmas` gives `pi_T' = 1`, while `abel_ts` gives
`ts_T' = 3`. The required player/share bridge would be `1 = 3`. Phase 3 must
replace the interface with a four-seat interface and migrate the profile before
it defines a run.

These facts do not yet prove an executed security failure. In particular,
commuting generators alone do not imply privacy failure. A `ShuffleMarginalBound`
at one word length is also not a protocol privacy theorem.

The Abelian phase must first compile the precise negative target in Section 6.7.

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

- an S5 deterministic correctness plug built from `s5_procs`
- an S5 randomized security plug built from the layout used by `s5_rprocs`
- an S5xS5 deterministic correctness plug built from `s5x5_procs`
- an S5xS5 randomized security plug built from the layout used by
  `s5x5_rprocs`
- a four-seat Abelian interface and revised coherent profile
- an Abelian secret-recovery plug using `ts_encode abel_ts`
- an Abelian shuffle-analysis plug using identity card content

Each probe must establish that the chosen players, fuel, process list,
termination fact, endpoint count, and reconstruction equation have the exact
types required by `ExecutionPlug`.

For each randomized plug, probe termination, endpoint count, and recovery of
the randomized secret. A process-list equality with the deterministic plug is
not expected and must not be assumed. If a generalized definition can share the
process skeleton without duplicating it, prefer that implementation. The two
plugs remain distinct public values.

The Abelian probe must confirm that the old player/share bridge is false. It
must then define an `abel_PI` with four starts and `pi_T' = 3`, revise
`abel_profile` so its interface and `abel_ts` agree, and compile every affected
consumer. Both Abelian plugs must satisfy the revised profile.

### 6.4 ObservedExecution probes

Probe one `ObservedExecution` for every execution path used by a public theorem.
Report its:

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

- S5 randomized exact-secrecy model on the randomized plug
- S5 finite-word endpoint model, with its plug and reader named explicitly
- S5xS5 randomized exact-secrecy product model on the randomized plug
- S5xS5 pile-one and pile-two finite-word endpoint models
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
- whether the generic transfer theorem has both of its actual premises at the
  required base-distribution carrier

Any mismatch must be stated as a new proof obligation. An endpoint pushforward
bound is not a bound on the underlying cut distribution and cannot discharge
the generic theorem for a coalition reader. Do not hide such a mismatch with a
cast, a renamed alias, or an unchanged numeric constant.

### 6.7 Abelian negative-result probe

The primary target is a negative mixing theorem for positive word length. Let
the actual distribution be the pushforward of the uniform length-`L.+1` word
distribution through the Abelian word evaluator. Let the ideal distribution be
uniform on the concrete four-element generated group. The target is that the
full-L1 distance between their complete executed endpoint-vector observations
is exactly `1`.

Phase 0 must compile the exact carrier, group-uniform distribution, word
distribution, endpoint-vector reader, and quantifier order. It must separately
prove or probe:

- the generated group is Abelian
- the two disjoint transpositions generate four elements
- fixed positive word length reaches one parity class of two elements
- the shuffle-analysis plug uses identity content, so its complete endpoint
  vector is injective on the generated permutation group
- the exact group-distribution distance is preserved by that reader

This target is `NEEDS-PROBE`. If its constant, parity scope, or carrier is
false, return NO-GO for Phase 3 and propose the smallest corrected statement in
the response. Do not silently substitute a different security notion.

The selected statement must satisfy all of these conditions:

- its ideal distribution is named and mathematically justified
- its actual distribution is the one used by the Abelian `SampleAdapter`
- its observer is finite and connected to the interpreter execution
- its distance is the exact full-L1 value `1` at positive word length
- the proof does not infer the result from commutativity alone
- the theorem is labelled as a mixing, anonymity, or privacy limitation
  according to its actual statement

If the target is mathematically false, return NO-GO for Phase 3. Do not replace
it with a vague theorem about search-space size.

### 6.8 Facade and manifest probe

Probe the final import graph for:

- `s5_analysis.v`
- `s5x5_analysis.v`
- `abelian_analysis.v`
- the updated repository manifest
- the clean one-import client

The probe must show that no import cycle is introduced and every proposed alias
can be checked from the manifest import.

The probe must also include the `_CoqProject` entries for every new production
file. Use qualified names for existing collisions such as
`s5_run.s5_players` and `s5_trace.s5_players`.

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

Construct two `ExecutionPlug s5_profile` values.

The deterministic correctness plug reuses:

- `s5_run.s5_players`
- `s5_procs`
- fuel 150, unless the probe proves another existing constant is authoritative
- `s5_run_terminates`
- `s5_endpoints`
- `s5_endpoints_size`
- `s5_run_recovers`

The randomized security plug uses the randomized layout currently evaluated by
`s5_rprocs`. Its input carrier must retain enough tape data to define both the
dealt layout and `rsh_secret s5_rs`. Generalize the run skeleton to take a cut,
and prove that its identity-cut specialization is `s5_rprocs`. Define the
explicit ordinal codec from the `'Z_5` randomized secret to the profile secret
carrier `'I_5`, and prove its cancellation facts. Prove new termination,
endpoint-count, and recovery facts for this plug. The recovered value must equal
the encoded randomized secret.

Do not claim that the two process lists are equal. They share a profile and a
session skeleton, but their dealt contents differ.

If concrete player lists are retained for reduction speed, add a comment that
states their computational role. Do not replace them with `enum` without a
timed reduction probe.

### 7.3 Observers

Construct one `ObservedExecution` for each plug. Expose at least:

- one seat endpoint
- one coalition endpoint view
- one finite content-trace reader on the randomized plug that matches
  `s5_player_trace`
- verifier endpoints
- raw trace extractors for navigation only

Prove the finite reader equalities required to identify `s5_player_trace` and
the coalition reader with the randomized executed observations. The
deterministic reader does not witness those secrecy theorems.

### 7.4 Models

Construct these S5 sample paths:

1. a randomized exact-secrecy model on the randomized security plug
2. a finite-word endpoint model for the distribution bounded by the landed
   spectral theorem

The randomized secrecy adapter uses the identity-cut point distribution because
the landed executed theorem is stated for `s5_rprocs`. Generalizing the process
definition to arbitrary cuts supports the package, but it does not broaden the
secrecy theorem without a new proof.

If the existing secrecy result and ideal model use a randomized-sharing space
rather than a group-uniform sample space, keep that distinction explicit. Do
not call two definitionally different priors equal without a theorem.

Expose the distribution equations needed by each path. Do not claim that the
finite-word endpoint model is a finite approximation of the randomized secrecy
model unless a new base-distribution theorem proves that relation.

### 7.5 Correctness

Transport the current facts through the deterministic package. Prove the same
three properties independently for the randomized package. The facade must
identify which correctness theorem belongs to which plug.

### 7.6 Security

Bridge the strongest existing S5 results that match the randomized adapter and
executed readers. At minimum, include:

- executed single-seat trace secrecy
- executed coalition view secrecy below the proved threshold
- the quantitative finite-word one-endpoint mixing bound as a separate bound
  capability conditional on `s5_rayleigh_Q2_R`

Do not describe endpoint mixing as coalition privacy. This request does not
require finite-word coalition privacy because the current bound does not supply
the base-distribution premise needed for that claim.

### 7.7 Transfer

The exact-secrecy path must expose `StaticExecutedOnly` and its reader equality.
The finite-word endpoint path must expose `NoModelComparison` unless Phase 0
proves the exact two premises of `var_dist_fdistmap_transfer` at the required
carrier. Do not specialize the generic theorem from an endpoint pushforward
bound. No ideal-to-finite coalition claim is an acceptance condition.

### 7.8 Public API

Add an S5 facade with the seven fixed sections. Add one manifest row per S5
analysis path. At minimum, use these rows:

| Row | Plug | Model | Capability | Transfer status |
|---|---|---|---|---|
| S5 deterministic correctness | deterministic | none | recovery | `NoModelComparison` |
| S5 randomized exact secrecy | randomized | randomized sharing | executed trace and coalition secrecy | `StaticExecutedOnly` |
| S5 finite-word endpoint | deterministic | finite generator words | conditional endpoint marginal bound | `NoModelComparison` |

Every row must name the exact observer, assumption status, and theorem
capability.

## 8. Required Phase 2: S5xS5 complete analysis path

Phase 2 begins only after the S5xS5 probes return GO.

### 8.1 Program and execution

Keep `s5x5_profile`. Construct two execution plugs.

The deterministic correctness plug reuses:

- `s5x5_run.s5x5_players`
- `s5x5_procs`
- the existing fuel
- `s5x5_run_terminates`
- `s5x5_endpoints`
- `s5x5_endpoints_size`
- `s5x5_run_recovers`

The randomized security plug uses the product tape and layout currently
evaluated by `s5x5_rprocs`. Its input carrier must retain the two randomized
sharing tapes. Generalize the run skeleton to take a cut, and prove that its
identity-cut specialization is `s5x5_rprocs`. Its reconstruction result is the
profile secret in `'I_10`, obtained by `combine_secret` from the two pile
secrets. Prove termination, endpoint count, and recovery of that combined
secret.

The security secret remains `JointSecret : 'Z_5 * 'Z_5`. Do not claim that
`combine_secret` is injective or that recovering its `'I_10` image recovers all
25 product-secret values. Secrecy about `JointSecret` comes from the executed
reader bridge, not from the `ObservedExecution` recovery field.

An arbitrary product tape need not satisfy `product_valid` for its
`combine_secret` image because `split_combineK` is partial. Therefore the
randomized recovery proof must work directly from the two factor sum
reconstructions and pile-preserving permutation action. It must not assume
`ts_valid s5x5_scheme` without proving it.

Do not flatten the two piles in the public statements merely to reuse S5 names.
Do not identify the deterministic `'I_10` secret with the product randomized
secret without a compiled codec and cancellation theorems.

### 8.2 Observers

Construct one `ObservedExecution` per plug. On the randomized plug expose at
least:

- a pile-one seat observer
- a pile-two seat observer
- a pile-one coalition observer
- a pile-two coalition observer
- a joint coalition observer
- finite trace readers used by the landed secrecy results
- verifier endpoints

The types must retain pile membership, coalition bounds, and joint structure.

### 8.3 Models

Construct a randomized exact-secrecy product path on the randomized plug.
Construct separate pile-one and pile-two finite-word endpoint paths on the
deterministic plug. Expose the joint distribution only for the randomized
secrecy path whose theorem uses it.

The randomized product adapter uses the identity-cut point distribution of the
landed trace theorem. Do not quantify its secrecy result over arbitrary cuts
without a new theorem.

Do not infer joint independence from two marginal bounds. A joint theorem needs
the exact product or coupling fact required by its statement.

### 8.4 Correctness

Transport the existing deterministic facts. Prove termination, endpoint count,
and recovery of the `combine_secret` image for the randomized package.

### 8.5 Security

Bridge at least:

- executed pile-one secrecy
- executed pile-two secrecy
- executed joint view secrecy under the proved coalition constraints
- pile-one and pile-two finite-word endpoint mixing bounds, each conditional on
  `s5_rayleigh_Q2_R`
- the exact full-L1 floor between each pile-uniform distribution and global
  uniform on ten seats
- the reverse-triangle lower bound from each actual endpoint distribution to
  global uniform, at word lengths where the resulting bound is positive

Preserve the distinction among `s5x5_pile1_TV_bound`,
`s5x5_pile2_TV_bound`, and `s5x5_spectral_TV_bound`.

`s5x5_spectral_TV_bound` is a one-seat endpoint theorem with a non-vanishing
`1 + ...` upper bound. It is not a joint theorem and must not be labelled as
one. This request does not require a new joint finite-word privacy theorem.

### 8.6 Transfer

The randomized secrecy row uses `StaticExecutedOnly` and must supply per-pile
and joint reader equalities. Each finite-word endpoint row uses
`NoModelComparison` for its upper bound to pile uniform. The two
global-uniform limitation rows use `NegativeTransfer`: combine the exact
pile-uniform floor with the conditional endpoint upper bound by the reverse
triangle inequality. State the positive-bound regime explicitly. Do not lift
two marginal bounds to a joint claim, and do not invoke the generic
ideal-to-finite theorem without its base-distribution premise.

### 8.7 Public API

Add an S5xS5 facade with the seven fixed sections. Add one manifest row per
analysis path. At minimum, use these rows:

| Row | Plug | Model | Capability | Transfer status |
|---|---|---|---|---|
| S5xS5 deterministic correctness | deterministic | none | recovery | `NoModelComparison` |
| S5xS5 randomized joint secrecy | randomized | product randomized sharing | executed per-pile and joint secrecy | `StaticExecutedOnly` |
| S5xS5 pile-one finite word | deterministic | finite generator words | conditional pile-one endpoint bound | `NoModelComparison` |
| S5xS5 pile-two finite word | deterministic | finite generator words | conditional pile-two endpoint bound | `NoModelComparison` |
| S5xS5 pile-one global limitation | deterministic | finite generator words | conditional positive endpoint-distance lower bound | `NegativeTransfer` |
| S5xS5 pile-two global limitation | deterministic | finite generator words | conditional positive endpoint-distance lower bound | `NegativeTransfer` |

The rows must keep per-pile and joint capabilities distinct and must state
their assumption status.

## 9. Required Phase 3: Abelian complete negative analysis

Phase 3 begins only after one Abelian negative target returns GO.

### 9.1 Program

Replace the incoherent interface inside `abel_profile`.

Define `abel_PI` as a four-seat `PGGInterface` over the same Abelian group,
using the four starting positions in canonical order. Revise `abel_profile` to
contain `abel_PI` and the existing `abel_plug`. Preserve the public name
`abel_profile` only after the new definition typechecks. Update
`profile_k_abel` and every consumer.

The old `Gen_PGG_2 abel_sigmas` value is a two-generator interface, not a
four-seat protocol interface. It may remain in group-level code under its old
role, but it must not be the `mp_PI` of the protocol profile. Do not interpret
the threshold value as a security proof.

### 9.2 Execution

Define two Abelian piSMC executions using the revised coherent profile and
shared program flow.

The secret-recovery plug deals `ts_encode abel_ts s`. It proves termination,
endpoint count, and recovery for every `s : 'I_4`.

The shuffle-analysis plug uses identity card content and a trivial run input.
Its complete endpoint vector therefore records the cut permutation on all four
starts. It proves termination and endpoint count. Its recovery theorem states
the actual constant value obtained by applying `abel_ts` reconstruction to the
identity layout under an Abelian group cut. Compute and name that value in the
probe. Do not claim arbitrary-secret recovery for this plug.

Both executions must use the actual Abelian generators and reconstruction plug.
Neither may reuse S5 execution under an unproved cast.

### 9.3 Observers

Construct one `ObservedExecution` per plug. Expose:

- seat endpoints
- the complete four-endpoint observer of the shuffle-analysis plug
- verifier endpoints
- a finite content reader when it is used by a secrecy or leakage statement
- raw traces for navigation only

The negative observer must be the executed four-endpoint vector of the
identity-content plug. Prove that its static reader is injective on the concrete
generated group.

### 9.4 Models

Construct at least:

1. the uniform distribution on the four-element generated permutation group,
   attached to the shuffle-analysis plug
2. the uniform positive-length generator-word distribution, attached to the
   same plug

Use a complete endpoint-vector observation that is injective on the generated
group. Name the word distribution, positive length parameter, parity data, and
executed observation distribution. Use the full-L1 convention.

### 9.5 Correctness

Prove arbitrary-secret recovery for the secret-recovery plug. Prove the named
constant recovery fact for the identity-content shuffle-analysis plug. The
facade must keep these results on their respective paths.

### 9.6 Negative security or mixing result

Prove the Phase 0 exact-distance statement. The result must end at the named
complete executed endpoint-vector observer.

The preferred proof chain is:

```text
commuting or orbit structure
  -> word evaluation invariant
  -> support or distinguishability fact for the actual sample model
  -> finite static observation limitation
  -> executed observation equality
  -> exact full-L1 distance 1
```

`abel_gens_commute`, `abelian_word_eval`, `freq_vec_det`, and
`abelian_search_space_bound` may support the proof. None of them alone is the
final negative result.

Do not call the theorem privacy failure when it proves only failure to mix to a
chosen ideal distribution. Use the narrowest accurate capability label.

### 9.7 Transfer

The Abelian transfer section uses `NegativeTransfer`. It must connect the parity
invariant and exact group-distribution distance to the executed endpoint-vector
distance. It need not state a positive ideal-to-finite security theorem.

Expose the group-distribution form, the static endpoint-vector form, the
executed form, and the equalities connecting them.

### 9.8 Public API

Add an Abelian facade with the seven fixed sections. Add at least these rows:

| Row | Model | Capability | Transfer status |
|---|---|---|---|
| Abelian secret recovery | none | arbitrary-secret recovery | `NoModelComparison` |
| Abelian identity-content correctness | none | constant recovery and endpoint observation | `NoModelComparison` |
| Abelian fixed-word limitation | uniform positive-length words versus group uniform | exact executed endpoint distance 1 | `NegativeTransfer` |

Label the second capability as a fixed-length mixing limitation, not as privacy
failure and not as an unqualified protocol failure.

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

Every Transfer section must expose at least one typed transfer-status alias.
PGL27 keeps its current model-transfer theorem. Five-card receives a
`StaticExecutedOnly` status alias but no fabricated theorem. PGL27 and
five-card otherwise keep their current public names and mathematics.

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
- assumption status, either `KernelClosed` or a list of named accepted
  assumptions

Define typed `CompletionLevel`, `TransferStatus`, and `AssumptionStatus` values.
Each manifest row is a small typed witness record for its profile, execution,
observation, and model levels. Theorems remain facade aliases and are checked by
spelled types. The source table may summarize rows, but it does not determine
their levels.

The manifest need not store arbitrary theorem proofs in one dependent record.
It must store the typed status values and compile-check every theorem alias
named by the source row. Do not claim that the source table itself is a
kernel-level registry.

### 10.3 Clean client

Update the one-import client so it reaches one representative alias from every
section of every implemented facade. An empty mathematical Transfer section is
represented by its typed transfer-status alias. Keep instance namespaces
distinct.

### 10.4 Completeness check

Add a reproducible check over tracked files below `pgg-smc/instances`. It finds
top-level global `Definition` declarations whose declared type is
`MonodromyProfile`, plus direct global aliases whose body is one of those
definitions. Exclude comments, `Local` declarations, facade aliases, probe
directories, documentation, backups, and generated files. Classify each result
as:

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

Add these production files to `_CoqProject` in dependency order:

- the S5 execution/model additions and `s5_analysis.v`
- the S5xS5 execution/model additions and `s5x5_analysis.v`
- the Abelian execution/model additions and `abelian_analysis.v`
- the revised manifest and clean client

The completion report must list the exact entries and import edges.

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

Every in-scope declaration must have exactly one repository role tag:

- facade aliases and other `Definition`s use `@intent:`
- helper lemmas use `@composes: <public-target>`
- public correctness theorems use `@main correctness:`
- public secrecy, leakage, and limitation theorems use `@main security:`
- endpoint and mixing bounds use `@main bound:`
- package-coherence theorems use `@main architecture:` when they are public

The descriptive terms above are not new `@main` labels. Names with five or more
underscore-separated components require a canonical MathComp suffix or a
`Naming:` justification accepted by I001.

## 12. Soundness requirements

1. Add no `Axiom`, `Parameter`, `Admitted`, or `Abort` to permanent sources.
   Preserve and disclose inherited assumptions. Do not duplicate or generalize
   `s5_rayleigh_Q2_R`.
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
20. Do not claim that a theorem conditional on `s5_rayleigh_Q2_R` is
    kernel-closed. Keep that assumption visible in facades, manifest rows, and
    the completion report.

## 13. Phase acceptance conditions

### 13.1 S5

S5 passes only if:

- deterministic and randomized `ExecutionPlug` values compile
- both `ObservedExecution` values compile
- randomized secrecy and finite endpoint adapters compile
- deterministic correctness is transported and randomized correctness is proved
- single-seat and coalition secrecy reach randomized executed observers
- the finite endpoint bound is labelled conditional on `s5_rayleigh_Q2_R`
- the rows use their exact transfer statuses and make no finite-word coalition
  claim
- its facade and manifest rows compile from the clean client

### 13.2 S5xS5

S5xS5 passes only if:

- deterministic and randomized `ExecutionPlug` values compile
- both `ObservedExecution` values compile
- pile and joint observers retain their types
- randomized product and per-pile finite adapters compile
- deterministic recovery is transported and randomized recovery of the
  `combine_secret` image is proved
- per-pile and joint secrecy reach randomized executed observers
- endpoint bounds and exact global-uniform floors remain distinct
- the derived global-uniform lower bounds state the non-vacuous word-length
  regime
- all spectral bounds name `s5_rayleigh_Q2_R`
- no joint finite-word privacy theorem is claimed
- its facade and manifest rows compile from the clean client

### 13.3 Abelian

Abelian passes only if:

- the four-seat `abel_PI` and revised `abel_profile` compile
- its secret-recovery and identity-content `ExecutionPlug` values compile
- both `ObservedExecution` values compile
- ideal and actual sample adapters compile
- arbitrary-secret and identity-content correctness are proved on their
  respective paths
- the positive-length word model has exact full-L1 distance `1` from group
  uniform at the complete executed endpoint observer
- the theorem is labelled as a fixed-length mixing limitation
- its facade and manifest rows compile from the clean client

### 13.4 Repository

The repository passes only if every in-scope profile is represented by a
complete facade or a documented alias of one. Every facade has seven sections
and a typed transfer-status alias. A path with `NoModelComparison` or
`StaticExecutedOnly` is complete for its stated capability and does not pretend
to contain an ideal-to-finite theorem.

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
21. the typed row matrix with completion, transfer, and assumption statuses
22. every theorem that depends on `s5_rayleigh_Q2_R`
23. the old and new Abelian interface/profile definitions and all migrated
    consumers

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
- eliminating or kernel-expanding `s5_rayleigh_Q2_R`
- finite-word S5 coalition privacy from the current endpoint bound
- joint finite-word S5xS5 privacy from the current marginal bounds

## 17. Final acceptance statement

The entire request is complete only when the formalization supports this
statement:

> PGL27, the five-card family, S5, S5xS5, and Abelian each have one typed public
> facade. Every facade separates its coherent execution paths, finite
> observations, probability models, correctness results, and strongest
> justified positive or negative analyses. Each path states its completion,
> transfer, and assumption status. The common navigation template preserves
> different observer types and theorem meanings.

It must also make this limitation explicit:

> A common analysis template organizes evidence. It does not make different
> protocols satisfy the same security theorem, and it does not make security an
> automatic consequence of filling `MonodromyProfile`.

## 18. Adversarial audit disposition

This revision incorporates the two NO-GO reports run against commit
`6117480e`. It still requires a fresh independent re-audit before an
implementation plan.

| Audit finding | Revision |
|---|---|
| Abelian requires the false bridge `1 = 3` | Phase 3 now replaces the two-seat profile interface with a four-seat `abel_PI` and migrates all consumers. |
| S5 correctness and secrecy use different executions | Phase 1 now requires distinct deterministic and randomized plugs, with new randomized correctness and reader bridges. |
| S5xS5 correctness and secrecy use different executions and secret carriers | Phase 2 now requires distinct plugs, uses `combine_secret` only for reconstruction, and keeps `JointSecret` as the security secret. |
| Endpoint marginal bounds cannot discharge generic coalition transfer | S5 and S5xS5 finite-word rows no longer claim coalition or joint privacy and do not invoke the generic theorem without its base-distribution premise. |
| S5xS5 has no joint finite-word theorem | The requirement was removed. Per-pile upper bounds and derived global-uniform lower bounds are separate rows. |
| Abelian lacked a pinned negative statement | Section 6.7 now pins the positive-length parity target and exact full-L1 distance `1`, subject to compiled probes. |
| Five-card has an empty Transfer section | Every facade now exposes a typed transfer-status alias. Five-card uses `StaticExecutedOnly`. |
| Completion levels and row cardinality were ambiguous | Sections 3, 7.8, 8.7, 9.8, and 10 define the status vocabulary and minimum row matrix. |
| Manifest level was comment-only | Phase 4 now requires typed completion, transfer, and assumption status values, with theorem aliases checked by type. |
| Completeness scan universe was ambiguous | Section 10.4 fixes the tracked root, declaration class, and exclusions. |
| New files and name collisions were missing from migration | Sections 6.8 and 10.4 require `_CoqProject` entries and qualified colliding names. |
| H/I comment grammar was underspecified | Section 11 maps declaration roles to the allowed tags and requires Naming justification where I001 applies. |
| `s5_rayleigh_Q2_R` is inherited by spectral results | Per the project decision, it remains a trusted certificate boundary because kernel expansion is computationally impractical. Every dependent capability is conditional and names it. |

The audits also found other inherited group-order and geometric-realisation
assumptions in the rigidity developments. This revision does not assign them the
Rayleigh certificate's efficiency rationale. It requires their exact disclosure
where `Print Assumptions` reports them.
