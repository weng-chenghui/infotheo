# Rocq formalization request: layered protocol packing and field migration

Date: 2026-08-12. Amended after commits `2376b3bd`, `74726029`,
`c4f159b2`, and `5439a34e` landed. Amended again after two independent
adversarial audits returned NO-GO on the earlier draft. Amended after the
centralization review to add typed facades, a completion manifest, and a
phased migration for the remaining instances.

Request path:
`docs/superpowers/requests/2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`

Status: REQUEST ONLY. This document does not authorize edits to the WADT paper.
The formalization tool must evaluate and probe the design before it writes an
implementation plan. It may implement the accepted design only after returning
an explicit GO verdict for the required stages.

The current revision has folded back the two NO-GO reports. It has not yet
passed the required re-audit. In particular, Sections 10.1, 10.2, 12, and 13
carry explicit `NEEDS-PROBE` gates.

## 1. Goal

Refactor the current group-parametric card-protocol formalization so that one
program profile can support several execution and shuffle analyses without
duplicating the piSMC program.

The intended dependency chain is:

```text
MonodromyProfile
  -> ExecutionPlug
  -> executable piSMC run
  -> observed execution package
  -> SampleAdapter
  -> executed observation distributions
  -> explicit bridges to exact or finite-shuffle security results
```

The central distinction is:

- `MonodromyProfile` describes the algebraic program family.
- `ExecutionPlug` supplies the operational data needed by the shared piSMC
  flow.
- `SampleAdapter` supplies a probability model for executions.
- Security certificates are separate values attached to a chosen probability
  model.

The completed design must support several shuffle analyses for one executable
program. Changing a shuffle distribution, bias, or word length must not create
a new piSMC program profile when the processes are unchanged.

## 2. Motivation

The shared piSMC exchange flow is stable across the group-parametric family:

```text
dealer sends hands
  -> each participant selects one hand entry
  -> each participant reveals one endpoint
  -> the verifier collects the endpoints
```

The current `MonodromyProfile` also stores one `SecurityWitness`. This mixes a
program description with one probability model. The problem is visible in two
current instances:

1. `five_card_exec_procs_biasE` proves that the five-card process list is
   independent of the bias and word length, although the current
   `five_card_profile` varies with both.
2. The PGL program uses one profile whose security witness describes the
   uniform group distribution, while the 200-letter word distribution is
   supplied separately by a `SampleAdapter`.

The current packing therefore gives the impression that a program has one
distinguished shuffle distribution, while the formal development actually
studies several distributions for the same program.

This request adopts the thin-package strategy. It preserves the current
algebraic, execution, and probability definitions where they are useful. It
adds one outer index and the missing bridge theorems. It does not rewrite every
security theorem as a record projection.

The thin packages still need one public navigation path. This request therefore
also requires typed facade files for the two featured instances and one
repository-level manifest that re-exports those facades. The facades organize
existing and newly bridged objects. They do not introduce a record that stores
every theorem about an instance.

## 3. Preconditions and live sources

This request assumes that the current `ExecutionPlug` and `SampleAdapter` work
has been completed and committed. The expected live files are:

- `pgg-smc/protocol/pgg_monodromy_profile.v`
- `pgg-smc/protocol/pgg_execution_plug.v`
- `pgg-smc/security/pgg_sample_adapter.v`
- `pgg-smc/instances/pgl27/pgl27_exec.v`
- `pgg-smc/instances/kim2025/five_card_exec.v`

If these files are still being edited in another worktree or task, stop. Do
not reimplement or overwrite that work. Record the blocking commit or dirty
state in the evaluation report.

The evaluator must also read:

- `docs/superpowers/requests/2026-08-11-monodromy-profile-end-to-end-ROCQ-formalization-response.md`
- `docs/superpowers/plans/2026-08-12-s5-w45-sample-law-input-trace-spec.md`
- `pgg-smc/instances/pgl27/pgl27_mixing.v`
- `pgg-smc/instances/pgl27/pgl27_word_privacy.v`
- `pgg-smc/instances/kim2025/five_card_kim.v`
- `pgg-smc/instances/kim2025/kim_input_privacy.v`
- `pgg-smc/instances/denboer1989/denboer_trace.v`

The amended baseline already contains the following results. Treat them as
prerequisites to preserve and migrate, not as results that this request still
asks to create:

- generic `exec_dealer_trace`, `fdistmap_prodr`, and `sa_joint_dist`
- `pgl27_sample_cut_distE`
- `pgl27_word_sample_coalition_distE`
- `pgl27_word_cut_distE`
- `pgl27_word_sample_joint_distE`
- `five_card_sample_cut_distE`
- `five_card_exec_input_raw_traceE` and
  `five_card_exec_input_trace_secrecy`
- `five_card_exec_dealer_raw_traceE`, `five_card_exec_dealer_traceE`,
  `five_card_exec_dealer_pair_centropy0`, and
  `five_card_exec_dealer_trace_centropy0`
- `den_boer_witness_rotationE` and `den_boer_sample_cut_witnessE`

The same landed cycle also added supporting declarations. Preserve them unless
a repeated usage audit proves that a helper can be made local or removed
without changing a public theorem:

- `five_card_card_bool2`
- `five_card_sample_uniform_prodE`
- `five_card_sample_snd_uniformE`
- `five_card_exec_traces_size`
- `five_card_exec_input_trace`
- `five_card_exec_dealer_raw_trace`
- `five_card_exec_dealer_readout`
- `five_card_exec_dealer_trace`
- `fdistmap_head1`
- `rho_from_words_weighted1`
- `kim_weight_uniform_at0`

This landed round advances the probability and observation prerequisites. It
does not add `ObservedExecution`, remove the deprecated fields, construct the
fixed-secret PGL adapters, construct the biased Kim adapters, extract the
generic exact-to-finite transfer theorem, or provide all public bridges in
Section 11. Those remain in scope.

The evaluation report must verify these names against the current `HEAD`.
If later commits rename or strengthen them, record the exact replacement
instead of recreating the old declaration.

Use `make -j1` for every build. Concurrent Rocq builds are forbidden in this
repository.

## 4. Architectural invariants

The implementation must preserve these boundaries.

### 4.1 Program data is independent of probability

After the migration, the program profile and execution plug must not depend on
a `realType` merely because a security witness does.

The target shape is conceptually:

```coq
MonodromyProfile
ExecutionPlug mp
SampleAdapter R mp e
```

The exact implicit arguments may differ if a probe shows that this shape does
not elaborate cleanly. Any replacement must preserve the same separation.

### 4.2 One program admits several analyses

One pair `(mp, e)` must support all of the following without reconstructing its
process terms:

- an exact uniform-group sample model
- a finite generator-word sample model
- a uniform five-card cyclic-cut model
- a single biased-cut model
- a repeated biased-cut model

Only the probability and security layers may vary between these models.

### 4.3 Execution correctness and security remain different claims

The outer package may derive execution termination, endpoint count, and output
recovery from explicit coherence facts. It must not call those results
security.

Exact privacy, approximate privacy, trace secrecy, entropy, and mutual
information remain separate certificates or theorems.

### 4.4 Packing must expose dependencies, not hide them

A field may store an instance fact when the fact cannot be derived generically.
The record and its comments must identify it as supplied data. Do not place an
instance theorem in a record and then describe it as framework automation.

## 5. Required stage A: separate the program profile from security

### 5.1 Remove `mp_security` from `MonodromyProfile`

The revised program profile must retain:

```text
mp_M
mp_secretT
mp_PI
mp_plug
```

It must no longer select a probability distribution or security certificate.

Consequences that the implementation must handle explicitly:

1. `MonodromyProfile` must no longer require `R : realType`.
2. `ExecutionPlug` must likewise become independent of `R`.
3. `profile_eps` and `profile_anonymous` must move out of
   `pgg_monodromy_profile.v` and become accessors or compatibility theorems of
   a separate marginal-bound value.
4. `profile_k`, `profile_private`, `run_recover`, and
   `profile_recon_encode` may remain profile-level operations because they are
   read from `mp_plug`, not from a probability model.
5. Every existing profile constructor must be migrated without changing its
   group, interface, reconstruction scheme, or executable process terms.
6. Generic execution functions such as `exec_run`, `exec_endpoints`, and
   `exec_decode` must lose their now-phantom explicit `R` argument.
7. `SampleAdapter` and distribution functions remain parameterized by
   `R : realType`, because they contain finite distributions.

The five-card program profile must become one probability-independent value:

```text
five_card_profile : MonodromyProfile
five_card_exec_plug : ExecutionPlug five_card_profile
```

Its type must not contain `R`, `eps`, positivity hypotheses, a spectral
hypothesis, or `L`. Den Boer and Kim may retain compatibility names, but every
such program-level wrapper must reduce or prove equal to this one core value.
Bias, hypotheses, and word length belong only to sample models and bound
certificates.

The PGL profile must likewise become independent of `R`. Its exact and word
sample models remain parameterized by `R`.

The implementation report must give two migration tables:

1. A before-and-after constructor table for PGL, five-card, den Boer, Kim, S5,
   S5xS5, abelian, and every other live `MonodromyProfile` value.
2. A before-and-after signature table for `MonodromyProfile`, `ExecutionPlug`,
   their smart constructors, the generic `exec_*` API, `SampleAdapter`, and the
   generic `sa_*` API. The table must account for every current explicit
   application whose argument list changes.

### 5.2 Keep shuffle bounds as separate certificates

Replace the current six-field `SecurityWitness` by two layers with these
required shapes. Exact universe arguments and implicit declarations may be
adjusted only if a probe requires it.

```coq
Record ShuffleMarginalBound (R : realType)
    (M : MonodromyReprWithGeneratorType) := MkShuffleMarginalBound {
  sw_L : nat;
  sw_bound_eps : R;
  sw_rho_dist : R.-fdist {perm 'I_(pgg_N' M).+1};
  sw_bound : forall s,
    var_dist (fdistmap (fun sigma => sigma s) sw_rho_dist)
             (fdist_uniform (card_ord (pgg_N' M).+1)) <= sw_bound_eps
}.

Record ShuffleCertificateBundle (R : realType)
    (M : MonodromyReprWithGeneratorType) := MkShuffleCertificateBundle {
  scb_bound : ShuffleMarginalBound R M;
  scb_exact : option (SecurityExact (sw_rho_dist scb_bound));
  scb_asymptotic : option (@SecurityAsymptotic R M)
}.
```

`SecurityExact` and `SecurityAsymptotic` remain as mathematical certificate
types. The second record preserves the current ability to attach either
certificate while keeping both optional attachments out of the always-present
marginal-bound record.

Perform an atomic source migration. A type alias alone is forbidden because it
cannot preserve the old `MkSecurityWitness` constructor arity. If a temporary
compatibility surface is necessary, it must include an explicit old-arity
constructor function and compatibility accessors, and its removal stage must
be recorded. New declarations must use `ShuffleMarginalBound` or
`ShuffleCertificateBundle` directly.

The generic constructor migration is fixed as follows:

- bound-only, fiber, direct-endpoint, entropy-bound, and solver constructors
  return `ShuffleMarginalBound`
- add `shuffle_bundle_of_bound`, which maps a marginal bound to a bundle with
  both optional attachments absent
- exact constructors return `ShuffleCertificateBundle` with `scb_exact = Some`
- Schreier constructors return `ShuffleCertificateBundle` with
  `scb_asymptotic = Some`
- Kim's constructor returns a bundle with both attachments present
- callers that require only `sw_L`, `sw_bound_eps`, `sw_rho_dist`, or
  `sw_bound` consume `scb_bound` or a `ShuffleMarginalBound` directly

The core record migration is also fixed:

- `AlgebraicRigidity.ar_security` becomes a `ShuffleCertificateBundle`
- `CombinatorialRigidity.cr_security` becomes a
  `ShuffleCertificateBundle`
- `SecurityProfile.sp_witness` becomes a `ShuffleMarginalBound`
- `CertifiedSolution.cs_witness` becomes a `ShuffleMarginalBound`
- landscape and dealer consumers reached through a rigidity record project
  `scb_bound` before reading `sw_*`

This preserves the existing exact or asymptotic attachment on a rigidity
instance while keeping bound-only APIs independent of optional certificates.

Use these instance-level target names unless the naming audit finds a concrete
collision:

- `pgl27_marginal_bound` replaces `pgl27_security`
- `fc_kim_security_bundle` replaces `fc_kim_security_witness`
- `kim_security_bundle_centi` replaces `kim_security_witness_centi`
- `den_boer_marginal_bound` names the bound projection of the unbiased,
  one-letter five-card bundle

Compatibility corollaries may retain theorem names such as
`profile_eps_pgl27` and `den_boer_perfect`, but their statements must read the
new bound values rather than a program profile.

The evaluator may propose a less nested representation only if a compiled
probe preserves these result types and attachment dependencies exactly.

The certificate must be attachable to a `SampleAdapter` or to its cut-image
distribution by an explicit equality. Merely storing two distributions with
similar names is not enough.

The new baseline makes this migration obligation concrete. The following
declarations currently mention `mp_security` directly:

- `pgl27_witness_cut_dist`
- `pgl27_sample_witness_prodE`
- `pgl27_sample_cut_distE`
- `five_card_witness_cut_dist`
- `profile_eps_pgl27`
- `den_boer_perfect`
- `den_boer_witness_rotationE`
- `den_boer_sample_cut_witnessE`

Move their right-hand sides to named, separate `ShuffleMarginalBound` values
for PGL and the five-card family, including the den Boer specialization.
`five_card_witness_cut_dist` currently has no consumer outside its own
declaration. The evaluator may remove that alias if a repeated usage audit
confirms this, but it must not remove the underlying Kim bound value.
Preserve the public equalities as compatibility theorems where useful.
Removing `mp_security` is incomplete if these results disappear, are weakened,
or are replaced only by similarly named distributions with no proved
equality.

### 5.3 Required repository-wide migration matrix

Before an implementation plan is written, inventory every declaration in the
following files that mentions `SecurityWitness`, `MkSecurityWitness`,
`sw_exact`, or `sw_asymptotic`:

```text
pgg-smc/reconstruct/algebraic_rigidity.v
pgg-smc/reconstruct/combinatorial_rigidity.v
pgg-smc/reconstruct/pgg_dealer_bridge.v
pgg-smc/reconstruct/pgg_protocol_landscape.v
pgg-smc/security/pgg_collusion_bound.v
pgg-smc/security/pgg_entropy_security.v
pgg-smc/security/pgg_entropy_security_demo.v
pgg-smc/security/pgg_schreier.v
pgg-smc/security/pgg_security_solver.v
pgg-smc/security/pgg_uniform_security.v
pgg-smc/security/pgg_sample_adapter.v
pgg-smc/protocol/pgg_monodromy_profile.v
pgg-smc/instances/abelian/rigidity_abelian_instance.v
pgg-smc/instances/cyclic/rigidity_cyclic_instance.v
pgg-smc/instances/kim2025/five_card_kim.v
pgg-smc/instances/monster/rigidity_monster_instance.v
pgg-smc/instances/oc/rigidity_oc_instance.v
pgg-smc/instances/pgl27/pgl27_group.v
pgg-smc/instances/pgl27/pgl27_profile.v
pgg-smc/instances/s5/rigidity_s5_instance.v
pgg-smc/instances/s5x5/rigidity_s5x5_instance.v
pgg-smc/instances/star/rigidity_star_instance.v
```

For each affected record, constructor, definition, and theorem, the matrix must
give its old type, target type, old constructor, target constructor, and any
compatibility path. At minimum it must cover `AlgebraicRigidity`,
`CombinatorialRigidity`, `SecurityProfile`, `CertifiedSolution`, all direct
`MkSecurityWitness` sites, and every generic smart constructor. A profile-only
constructor table does not satisfy this requirement.

## 6. Required stage B: remove or migrate obsolete fields

### 6.1 Remove `sw_exact`

The preflight usage audit found no theorem that projects and consumes
`sw_exact`. It does have live constructor producers. Kim, uniform security,
and `security_witness_with_exact` currently populate it.

Remove it only from `ShuffleMarginalBound`. Preserve `SecurityExact`, and move
the optional attachment to `ShuffleCertificateBundle.scb_exact` as fixed in
Section 5.2. Migrate every current producer. Do not replace a stored exact
certificate by an unconnected theorem about a different distribution.

Before removal, mutation-check the repository usage result with `rg` and a
constructor probe. If a live consumer has appeared, report it and revise this
stage before implementation.

### 6.2 Remove `sw_asymptotic`

The preflight usage audit found no projection consumer of `sw_asymptotic`.
It also has live constructor producers in Schreier, Kim, S5, S5xS5, and OC.
Preserve `SecurityAsymptotic`, and move the optional attachment to
`ShuffleCertificateBundle.scb_asymptotic` as fixed in Section 5.2. Migrate
every current producer.

Do not remove any existing asymptotic theorem. Only remove the unused optional
slot from the always-present marginal-bound record.

### 6.3 Remove `ep_cards_bridge` and the unused helper that requires it

`ep_cards_bridge` is consumed only by `exec_content_from_plug`, and the current
repository has no consumer of `exec_content_from_plug`. The PGL and five-card
execution plugs both supply reflexivity for this field.

The target change is:

1. Remove `ep_cards_bridge` from `ExecutionPlug` and its smart constructors.
2. Remove `exec_content_from_plug` if the preflight audit still finds no
   consumer.
3. If a live consumer has appeared, move the card/share equality to that
   helper or to a narrow compatibility record. Do not keep it in every
   `ExecutionPlug` solely for one optional helper.

Removing this field must not weaken the required seat/share coherence used by
the decoder.

### 6.4 Do not remove `sw_L`

`sw_L` is used by `pgg_dealer_bridge.v` and several constructions in
`algebraic_rigidity.v`. It is not dead metadata.

This request does not require relocating `sw_L`. A later refactor may move it
into a finite-word configuration, but the present implementation must preserve
all consumers.

## 7. Required stage C: retain meaningful fields and document why

The following fields may look redundant but must not be removed in this
request.

### 7.1 Retain `ep_players` and `ep_playersE`

`ep_playersE` proves that the concrete participant list is the canonical seat
enumeration. The concrete list is also a computational cache.

The earlier probe found that direct reduction of `enum 'I_8` becomes stuck
behind an opaque `idP` term and produces a large normal form. The concrete
eight-player list reduces in approximately 0.02 to 0.04 seconds. The formal
equality preserves the canonical mathematical meaning while the stored list
preserves tractable computation.

Add source comments with these meanings:

- `ep_players` is the concrete ordered seat list used by executable reduction.
- `ep_playersE` certifies that the cached list is exactly the canonical
  enumeration and gives no semantic freedom to omit or reorder seats.

The comments must not mention temporary implementation status. They must state
the stable API contract.

### 7.2 Retain `ep_players_bridge`

This equality connects the participant count to the reconstruction share
count. `exec_decode` requires it.

Add a source comment stating that it is the type-level coherence condition
between the piSMC seat tuple and the reconstruction tuple. Do not describe it
as privacy or dropout tolerance.

A future redesign may index `PGGInterface` by the scheme share count and make
this equality definitional. That redesign is outside the present request.

### 7.3 Retain `ep_fuel`

`ep_fuel` drives `run_interp` and the current executable termination proofs.
It is operational configuration, not mathematical protocol data.

Add a source comment stating that the field selects the interpreter evaluation
budget used by `exec_run`. The comment must also state that changing a
sufficient fuel value does not define a different algebraic profile.

Do not move it into a new `InterpreterConfig` in this request unless a probe
shows that the move is mechanical and does not disturb the instance proofs.

### 7.4 Retain the remaining execution-input fields

The following fields distinguish real executable families and must remain:

- `ep_inputT` is the carrier of one run argument. It may differ from the
  reconstructed secret type.
- `ep_content` turns a run argument and committed input payloads into the card
  content readout used by the dealer.
- `ep_input_procs` supplies the additional committing-party processes. It is
  empty for a dealer-secret instance and nonempty for a committed-input
  instance.

Add source comments with these meanings. In particular, do not describe
`ep_input_procs` as a group-dependent field. It records the input mode of the
protocol family.

### 7.5 Retain the four `SampleAdapter` fields

The fields have distinct roles:

- `sa_sampleT` is the finite carrier of random choices.
- `sa_sampleP` is the distribution on that carrier.
- `sa_arg` maps a sample point to the executable program input.
- `sa_cut` maps a sample point to the group element used by the run.

Add or retain source comments that state these roles. In particular,
`sa_sampleP` is not a distribution over interpreter results, and `sa_cut` may
evaluate a generator word before the run sees it.

Do not merge `sa_arg` and `sa_cut` merely to reduce the number of fields. A
product-valued map stores the same information and gives no semantic gain.

Retain the generic `sa_joint_dist` added in `2376b3bd`. Its explicit argument
reader is necessary because a finite distribution requires a finite codomain.
Its type does not require that reader to equal `sa_arg`. Add or retain a source
comment that calls it the joint distribution of a chosen finite-valued sample
observable and the evaluated cut. It must not call the generic reader the run
argument, a distribution over interpreter runs, or a distribution over raw
traces.

An instance theorem may call it the run-argument-and-cut distribution only
when it passes `sa_arg` itself, as `pgl27_word_sample_joint_distE` does, or when
it proves an explicit equality between the supplied reader and `sa_arg`.

### 7.6 Retain the core `MonodromyProfile` fields

Add or retain precise source comments:

- `mp_M` selects the finite group representation and its permutation action.
- `mp_secretT` is the dependent secret carrier used by the reconstruction
  plug. It permits profiles with different secret types.
- `mp_PI` supplies the participant count and starting positions for the shared
  exchange program.
- `mp_plug` supplies the reconstruction scheme and its group-invariance data.

The comments must not claim that these four fields alone construct a complete
run or prove security.

### 7.7 Retain and document the marginal-bound core

On `ShuffleMarginalBound`, add or retain source comments with these meanings:

- `sw_L` is the finite-word length consumed by existing dealer and rigidity
  constructions.
- `sw_rho_dist` is the analyzed distribution on permutation images.
- `sw_bound_eps` is the stated full-`L1` upper bound.
- `sw_bound` proves the bound separately for each starting position.

The comments must say that this is a per-position marginal guarantee. They
must not call it coalition privacy or protocol security.

### 7.8 Retain the generic trace extractors and document their observer scope

Retain `exec_participant_trace`, `exec_input_trace`, `exec_dealer_trace`, and
`exec_coalition_trace`. These are derived read-offs from `exec_run`, not new
record fields.

Add the missing definitional twin:

```text
exec_verifier_trace x w0 P_idx :=
  nth [::] (exec_run x w0 P_idx).2 exec_verifier_id
```

Then define `exec_endpoints` through `endpoints_of_trace` of this extractor, or
prove the corresponding definitional equality. This does not add a verifier
privacy theorem.

Their comments and downstream theorem comments must keep the observers
distinct:

- a participant coalition contains only the selected participant seats
- an input-party row is not a dealer row
- the dealer row is not part of a participant-coalition observation unless a
  theorem explicitly adds it
- the verifier row is distinct from its decoded endpoint list
- a raw `seq` trace is not itself a finite-distribution observable

For input rows, distinguish a valid input-process index from an arbitrary
`j : nat`. In the five-card instance only `j = 0` and `j = 1` denote committing
parties. Larger indices return the default empty row because they are outside
the run, not because a sender logs nothing.

The outer package may expose these derived functions, but it must not store
them again or imply that one coalition theorem covers every observer.

## 8. Deferred field splits

The evaluator must record, but not implement, these larger cleanups unless one
is required to make stages A through D typecheck.

### 8.1 `rp_content`

`rp_content` belongs to fixed-content covering and landscape constructions.
The new execution layer uses `ep_content` to support input-dependent layouts.
A future split may define a reconstruction core and a separate fixed-content
extension.

Do not remove `rp_content` now. It has live consumers in covering, landscape,
S5, and S5xS5 files.

### 8.2 `pi_starts_uniq`

Execution only needs the starting positions. Distinctness is consumed by
group-action and exact-privacy arguments. A future split may separate a basic
layout from a distinct-layout certificate.

Do not remove `pi_starts_uniq` now. It has live consumers in
`pgg_interface.v`.

### 8.3 `ep_players_bridge`

As stated in Section 7.2, a stronger dependent index may eventually replace
this equality. That is not part of the thin-package migration.

## 9. Required stage D: add a thin observed-execution package

Add one self-contained dependent record. It is not parameterized by an
external profile or execution plug. Its required skeleton is:

```coq
Record ObservedExecution := MkObservedExecution {
  oe_profile : MonodromyProfile;
  oe_execution : ExecutionPlug oe_profile;
  oe_P_idx : nat;
  oe_content_obs :
    ep_inputT oe_execution ->
    pgg_gT (mp_M oe_profile) * 'I_(pgg_N' (mp_M oe_profile)).+1 ->
    'I_(pgg_N' (mp_M oe_profile)).+1;
  oe_expected : ep_inputT oe_execution -> mp_secretT oe_profile;
  oe_terminates : forall x w0,
    (exec_run oe_execution x w0 oe_P_idx).1 =
    nseq (size (exec_procs oe_execution x w0 oe_P_idx)) Finish;
  oe_endpoints : forall x w0,
    exec_endpoints oe_execution x w0 oe_P_idx =
    exec_static_endpoints oe_execution oe_content_obs x w0;
  oe_static_recon : forall x w0,
    w0 \in pgg_G (mp_M oe_profile) ->
    forall Hsz :
      size (exec_static_endpoints oe_execution oe_content_obs x w0) =
      (pi_T' (mp_PI oe_profile)).+1,
      exec_decode oe_execution
        (exec_static_endpoints oe_execution oe_content_obs x w0) Hsz =
      oe_expected x
}.
```

The implementation may adjust explicit arguments and coercions, but it must
preserve this dependency order and these quantifiers. In particular,
`oe_execution` depends on `oe_profile`, and the three proof fields quantify
over every run argument and cut. Only reconstruction carries the group
membership hypothesis.

The package must derive through the existing generic theorem bodies:

- endpoint count
- executed output recovery for every group-valid cut
- the conjunction of termination, endpoint count, and recovery
- seat endpoint read-off
- coalition endpoint read-off

The package may expose `exec_participant_trace`, `exec_input_trace`,
`exec_dealer_trace`, `exec_verifier_trace`, and `exec_coalition_trace` by
specialization. It must not claim to derive a semantic trace equation from the
record fields. Raw-row-to-content or raw-row-to-view equations remain
instance-specific theorems in Sections 10 and 11.

The new record must not duplicate generic proof bodies or store derived trace
functions as fields.

Required concrete values:

- one PGL observed execution
- one five-card observed execution shared by den Boer and Kim shuffle models

The five-card value must not vary with bias or word length if its process terms
are definitionally or propositionally identical.

## 10. Required stage E: attach several probability models to one execution

Build named analysis values over the observed executions.

### 10.1 PGL models

Provide:

1. An exact model with the intended secret prior and uniform group shuffle.
2. A finite-word model with an arbitrary Boolean prior and a uniform
   200-letter word over the symmetrized generator alphabet.
3. A fixed-secret exact model parameterized by `s : bool`, whose sample
   distribution is the uniform group distribution and whose execution
   argument is constantly `s`.
4. A fixed-secret finite-word model parameterized by `s : bool`, whose sample
   distribution is the 200-letter word distribution and whose execution
   argument is constantly `s`.

The fixed-secret carriers are not left to implementation judgment:

- the exact carrier is `pgg_gT pgl27_M`, with the uniform distribution on
  `pgl27_G_pos`, constant argument `s`, and identity cut
- the word carrier is `200.-tuple 'I_5`, with `pgl27_word_wordP`, constant
  argument `s`, and cut `word_eval`

The first two models already have `pgl27_sample` and `pgl27_word_sample` as a
foundation. The amended baseline also proves their exact or word cut
distributions, the word executed-to-static coalition equality, and the joint
distribution of the arbitrary-prior secret and evaluated word cut. Reuse and
migrate these declarations. Do not create duplicate versions.

`pgl27_word_sample_joint_distE` concerns the secret and cut. It is not yet an
equality for the secret and executed coalition view. The fixed-secret models
also remain to be constructed.

The joint-prior models serve independence and joint-distribution theorems. The
fixed-secret models serve the pairwise view-indistinguishability theorem. Do
not use an arbitrary secret prior where the theorem compares two fixed
secrets.

After reusing the landed results, prove the remaining connections:

- preserve the exact cut distribution as the intended uniform group
  distribution through the `mp_security` migration
- preserve the finite-word cut distribution as `rho_word`
- complete any missing executed seat and coalition endpoint distribution
  equalities for the required models
- the joint executed view-and-secret observable equals the static observable
  used by the existing PGL independence or mixing theorem
- each fixed-secret executed coalition distribution equals the corresponding
  static coalition-view distribution used by `pgl27_word_view_indist`

The last item must be a Rocq equality or an exact rewrite chain. Similar names
or matching prose do not pass.

The trace bridge requires one named finite reader. Define a PGL execution
observer with codomain `{ffun 'I_8 -> 'I_8}` by applying `content_of` to each
selected participant's generic raw row and returning `ord0` outside the
coalition. Prove its pointwise equality to `pgl27_coalition_trace` after any
necessary seat-type transport. Then prove the corresponding fixed-secret word
distribution equality used by `pgl27_word_trace_indist`.

This finite reader is not the raw `exec_coalition_trace`. The equality and its
distribution corollary are `NEEDS-PROBE` before planning.

### 10.2 Five-card models

Provide separate values for:

1. The uniform cyclic cut used by den Boer.
2. Kim's single biased cut at a symbolic bias.
3. Kim's repeated biased cut at a symbolic word length `L : nat`.
4. The concrete bias `1/100`, length `7` endpoint-mixing instance.

Their carriers and maps are fixed as follows:

- uniform model: the landed `five_card_sample` over
  `Omega = bool * bool * 'I_5` and the uniform distribution `P`
- single biased model: the same `Omega`, sample distribution
  `kim_input_dist eps_lt_inv5 eps_gt_neg4inv5`, run argument the input pair,
  and cut `(fc_sigma ^+ k)%g`
- repeated biased model: carrier
  `(bool * bool) * L.-tuple 'I_5`, sample distribution the uniform input-pair
  distribution times `word_weighted (kim_weight_dist ...)`, run argument the
  input pair, and cut `word_eval`
- concrete model: the repeated model at bias `1/100` and length `7`

The adapter for the single biased model needs only the two positivity
hypotheses used by `kim_input_dist`:

```text
eps < 1/5
-4/5 < eps
```

The bridge to `kim_input_private` additionally requires:

```text
0 < 1/5 - |eps|
```

The repeated endpoint-bound bridge additionally carries the spectral
hypothesis `|eps| < 4/5` required by `fc_kim_security_bound`. Do not place
these probability hypotheses on `five_card_profile` or `five_card_exec_plug`.

The current `five_card_sample` already supplies the first model's uniform
rotation distribution, even when its execution plug is indexed by arbitrary
bias parameters. `five_card_sample_cut_distE` identifies that distribution,
and `den_boer_sample_cut_witnessE` ties it to the den Boer witness. Preserve
both facts during the `mp_security` migration.

This uniform sample is not Kim's biased single-cut or repeated-cut sample.
The latter models and their bridges remain required.

Prove or preserve the corresponding claims:

- its cut distribution is the intended uniform, biased, or repeated-cut
  distribution
- the uniform model's executed participant trace equals the existing den Boer
  finite trace observation used by the exact theorem
- the single biased model's executed colour observation equals `kim_view A`
- the repeated and concrete models' executed seat endpoint distributions equal
  the static endpoint pushforwards used by their marginal bounds

The single biased bridge must not equate `sa_coalition_view C` directly with
`kim_view A`. Their codomains and indexing conventions differ. Define this
finite executed colour reader first:

```text
five_card_exec_colour_view A ab w0 :=
  map_tuple
    (fun j => decode_bool (nth ord0
      (exec_endpoints five_card_exec_plug ab w0 0) j))
    (in_tuple A)
```

The exact syntax may change after elaboration, but the reader must retain all
of the following behavior:

- `A : seq nat`, including order and duplicates
- Boolean decoding of card positions
- the same `false` result as `ViewA` for an out-of-range natural index
- codomain `(size A).-tuple bool`

Prove a pointwise equality to `ViewA R A` at the rotation cut and then a random
variable equality to `kim_view A` under `kim_input_dist`. Only after these
equalities may the implementation transport `kim_input_private`. This reader,
its cut orientation, and the out-of-range equation are `NEEDS-PROBE` before
planning.

Preserve the new observer facts without misclassifying them:

- `five_card_exec_input_raw_traceE` says that a committing party's own row is
  empty under the current sender-logging semantics only at the two valid input
  indices
- `five_card_exec_input_trace_secrecy` is a constant-conditioning equality,
  not commitment privacy
- its all-`nat` statement also covers out-of-range rows through the default
  value and must say so separately
- the committed payloads appear in the dealer row
- `five_card_exec_dealer_pair_centropy0` says that the decoded dealer row
  determines both committed bits
- `five_card_exec_dealer_trace_centropy0` says that it therefore determines
  the conjunction secret

Participant-coalition privacy must not silently include or exclude the dealer
or input parties. Every bridge theorem must state its observer.

Do not claim a seven-cut coalition, trace, or conditional-mutual-information
theorem unless an existing theorem or a new proof establishes it. The current
seven-cut result is an endpoint-mixing result.

## 11. Required stage F: explicit analysis bridges

The completed dependency graph must contain public bridge theorems for the
paper's featured claims.

### 11.1 PGL exact bridge

Connect the exact `ObservedExecution` and its exact sample model to the existing
coalition-view independence theorem. The final exported theorem must mention
the executed observation or its distribution, not only `pgl27_view`.

### 11.2 PGL finite-word bridge

Connect the finite-word model to:

- `pgl27_word_mixing`
- `pgl27_word_view_indist`
- `pgl27_word_trace_indist`
- `pgl27_view_mixing`

At least one public theorem must show an end-to-end chain from the finite-word
sample model through the evaluated cut and executed observation to the
existing `2^-39` coalition-view result.

The `2^-39` theorem must use the two fixed-secret finite-word models required
by Section 10.1. The arbitrary-prior model is reserved for the joint
view-and-secret proximity theorem `pgl27_view_mixing`.

The trace theorem must use the finite execution reader required by Section
10.1. It must not place a finite distribution directly on
`exec_coalition_trace`.

Keep the distance convention unchanged. The repository's `var_dist` is the
full `L1` distance.

### 11.3 Five-card exact and biased bridges

Connect the uniform model to the existing den Boer exact view or trace secrecy
theorem.

Connect the single biased-cut model to `kim_input_private` through an exact
equality between `five_card_exec_colour_view` and `kim_view`. Carry the extra
small-bias hypothesis required by `kim_input_private`.

Connect the repeated-cut model to `fc_kim_security_bound` and the concrete
seven-cut model to `kim_deal_centi_lt` at the endpoint level.

Do not turn an endpoint marginal bound into input privacy by naming or record
packing.

The repeated and seven-cut exports are bound bridges. Their declaration
comments must use `@main bound`, not `@main security`, unless their formal
statements are strengthened by a separate security proof.

## 12. Required stage G: one generic exact-to-finite transfer theorem

Extract the proof shape used by `pgl27_word_view_indist` into a generic theorem
over finite distributions and two finite observables.

Pin and probe this statement shape before planning:

```coq
Variables (A B : finType) (P Q : R.-fdist A).
Variables (fx fy : A -> B) (delta : R).

Hypothesis HPQ : var_dist P Q <= delta.
Hypothesis Hideal : fdistmap fx Q = fdistmap fy Q.

Conclusion:
  var_dist (fdistmap fx P) (fdistmap fy P) <= delta + delta.
```

The proof should use the existing data-processing and triangle-inequality
lemmas. It must not depend on PGL, three-transitivity, or Boolean secrets.
The theorem must bind the common source carrier, both source distributions,
both observables, their common finite codomain, and `delta` explicitly.

Instantiate the theorem for PGL. The existing public theorem may remain as a
compatibility corollary. Do not change its constant from `2^-39`.

The generic theorem and its PGL instantiation are `NEEDS-PROBE`. The probe must
also remove `Hideal` and confirm that the conclusion no longer follows from
the remaining assumptions.

This theorem establishes a reusable proof principle. It does not make every
`SampleAdapter` secure. Each instance must still prove equality of the two
ideal view distributions and supply the finite-to-ideal shuffle bound.

## 13. Required stage H: typed facades and a completion manifest

The package chain in Sections 5 through 12 gives the formalization a dependency
spine. This stage gives users one stable route through that spine. It must not
merge different observers or security notions into one record.

### 13.1 Phase H1: featured-instance facades

Phase H1 is required by this request. Add one public facade file for PGL and one
for the five-card development. Use names that pass the repository naming audit.
The expected locations are conceptually:

```text
pgg-smc/instances/pgl27/pgl27_analysis.v
pgg-smc/instances/kim2025/five_card_analysis.v
```

An API probe may select different collision-free basenames. Record any change
in the completion report.

Each facade must present its public aliases in this fixed order:

1. Program
2. Execution
3. Observers
4. Models
5. Correctness
6. Security
7. Transfer

These are source sections and public namespaces or prefixes, not fields of one
large record. A facade alias must have the exact type of the value or theorem
that it exposes. Do not copy proof bodies into the facade. An alias to a proof
must use the existing proof term or a one-line exact theorem whose assumptions
and conclusion are definitionally the same.

The PGL facade must expose, at minimum:

- its probability-independent program profile and execution plug
- its `ObservedExecution` value
- the participant and coalition endpoint observers
- the finite content-trace observer required by Section 10.1
- the exact-uniform and finite-word sample models
- execution correctness and recovery
- the exact-security bridges
- the finite-word security bridges
- the PGL specialization of the generic transfer theorem

The five-card facade must expose, at minimum:

- its probability-independent program profile and execution plug
- its `ObservedExecution` value
- participant, coalition, input-party, dealer, and verifier observers
- the decoded sequence observer required for the Kim bridge
- uniform, single-biased, repeated-biased, and seven-cut sample models
- execution correctness and recovery
- each exact-security, entropy, trace, or input-privacy bridge that is actually
  proved
- repeated and seven-cut endpoint bounds under a `bound` heading, not a
  `security` heading

The observer aliases must preserve their distinct carriers and index domains.
The facade must not use one untyped list to erase the difference between an
endpoint observer, a raw trace, a finite trace reader, and the Kim decoded
sequence.

### 13.2 Completion levels

Use these cumulative completion levels when describing an analysis path:

1. `Algebraic`: a `MonodromyProfile` value exists.
2. `Executable`: an `ExecutionPlug` for that profile exists and exposes the
   shared piSMC run.
3. `Observed`: an `ObservedExecution` value and its named executed observers
   exist.
4. `Sampled`: a `SampleAdapter` connects a named probability distribution to a
   named executed observer.
5. `Security-bridged`: an explicit bridge reaches a theorem about the same
   distribution and observer under a stated security notion.

The level is assigned per analysis path, not once per protocol name. For
example, PGL exact-uniform and PGL finite-word analyses are separate paths.
Likewise, a five-card repeated or seven-cut path with only an endpoint marginal
bound remains `Sampled` with a bound capability. It must not be labeled
`Security-bridged` merely because a `ShuffleMarginalBound` exists.

Each claimed level must be witnessed by a public, type-checked alias in the
instance facade. Levels must not be stored as an unaudited enumeration whose
value can disagree with the available aliases. The manifest audit must infer
or validate the level from the required witnesses:

| Level | Required typed witness |
|---|---|
| `Algebraic` | profile alias |
| `Executable` | execution-plug alias indexed by that profile |
| `Observed` | observed-execution alias indexed by that profile and plug |
| `Sampled` | sample-adapter alias plus its distribution-to-observer bridge |
| `Security-bridged` | bridge alias to the named security theorem |

Record theorem capabilities separately from the level. Use a closed vocabulary
such as `correctness`, `exact privacy`, `approximate privacy`, `trace privacy`,
`conditional entropy`, `mutual information`, and `endpoint marginal bound`.
Do not collapse these capabilities into one generic `secure` label.

### 13.3 Repository-level typed manifest

Add one repository-level entry file, conceptually:

```text
pgg-smc/instances/pgg_analysis_manifest.v
```

The manifest must import and re-export the two Phase-H1 facades so that one
import reaches their public aliases. It must contain a compact source table
with one row per analysis path. Each row names:

- protocol family and model
- profile alias
- execution alias
- observed-execution alias
- sample alias
- observer alias and carrier
- bound or certificate alias, when present
- final bridge theorem alias, when present
- completion level
- exact theorem capability

The table is a navigation index, not a substitute for Rocq declarations. Every
identifier in it must resolve in a clean build. Add a deterministic checker or
compile-time `Check` block that fails when a listed alias disappears or changes
to an incompatible type. If a generated checker is used, commit both its source
and its reproducible invocation.

The manifest must make partial paths visible. A missing security bridge is
reported as an absent capability and a lower completion level. It must not be
filled with a dummy theorem, `option` proof, axiom, or placeholder.

### 13.4 Phase H2: remaining-instance migration

Phase H2 is a required follow-up design but is not an implementation gate for
this request. After H1 has compiled and its API has stabilized, inventory the
remaining profiles, including den Boer, Abelian, S5, S5xS5, OC, and any other
live `MonodromyProfile` constructor found by repository search.

For each remaining instance:

1. add a facade using the same seven-section order
2. expose only the typed witnesses that already exist
3. assign each analysis path its actual highest completion level
4. add the path to the repository manifest
5. leave missing execution, observation, sampling, or security work explicit

Phase H2 must not manufacture new execution or security proofs merely to raise
an instance's level. Any such proof obligation requires a separate
formalization request. The H1 completion report must produce the complete H2
inventory and proposed order, but it need not implement those facades.

### 13.5 H1 acceptance conditions

Phase H1 passes only if:

- a clean client can import the manifest and reach both featured facades
- all seven sections exist in both facades, with empty capability sections
  explicitly documented when a class of result is absent
- every manifest identifier resolves and every level matches its witnesses
- no theorem statement, observer carrier, assumption, or numeric bound changes
- no proof body is duplicated merely to populate a facade
- endpoint marginal bounds are not labeled as privacy or security
- importing the manifest introduces no dependency cycle
- the H2 inventory covers every live profile constructor

This stage is `NEEDS-PROBE` because the repository currently has no established
facade-module pattern and the exact import graph must be checked before the
filenames and aliases are fixed in an implementation plan.

## 14. Commenting requirements

The migration must improve source-level clarity. Apply all repository comment
rules and the following requirements.

### 14.1 Record-level comments

Each retained record must have a short declaration comment that says:

- what layer the record belongs to
- which earlier record it depends on
- what data a constructor supplies

The declaration comment must remain declarative. Put derived API summaries,
consumer lists, migration rationale, and statements about what the record does
not prove in the surrounding module overview or completion report, not in the
record declaration comment.

For example, the revised program profile comment must say that it supplies
group action, layout, and reconstruction data. It must not say that it supplies
a probability model or security theorem.

### 14.2 Field comments

Every retained field or generic API item whose necessity is not visible from
its type must have a source comment immediately before it or in the record's
field table.

Mandatory cases are:

- `ep_players`, including its computational-cache role
- `ep_playersE`, including canonical-enumeration coherence
- `ep_players_bridge`, including seat/share type coherence
- `ep_fuel`, including its interpreter-budget role
- `sw_L`, including the live word-length consumers
- `sw_rho_dist`, `sw_bound_eps`, and `sw_bound`, including their marginal-only
  scope
- `scb_bound`, `scb_exact`, and `scb_asymptotic`, including the fact that the
  latter two are optional attachments and do not change the core bound
- `mp_secretT`, including dependent heterogeneous secret types
- `ep_inputT`, `ep_content`, and `ep_input_procs`, including the distinction
  between run arguments, deck construction, and additional input parties
- all four `SampleAdapter` fields
- `sa_joint_dist`, including why it takes a finite argument reader
- the five generic raw-trace extractors listed in Section 7.8
- every `ObservedExecution` field, including the dependency of
  `oe_execution` on `oe_profile` and the group-membership scope of
  `oe_static_recon`

The comments must describe stable mathematical or computational meaning. Do
not write status narration such as "kept for now", "not removed", or "needed
by this refactor" in declaration comments.

### 14.3 Theorem comments

The body of every rendered theorem, lemma, definition, or record comment must
state what the object is. It must not contain proof strategy, progress status,
effort estimates, rejected alternatives, or paper-writing instructions.

Proof strategy and migration rationale belong in ordinary non-rendered source
comments or the completion report.

Apply the repository's role-tag grammar explicitly:

- each new multi-line `Definition` uses exactly one `@intent:` tag
- each helper lemma uses exactly one `@composes: target` tag
- each main lemma uses exactly one allowed label from `@main security:`,
  `@main correctness:`, `@main architecture:`, or `@main bound:`
- endpoint-marginal results use `@main bound:`
- migration status and rejected alternatives never appear in rendered
  statement comments

Apply the repository's naming audit to every new identifier. A long instance
name such as `five_card_exec_colour_view` must carry a substantive `Naming:`
line if the I-series rule requires one. The line must explain the semantic
prefix and suffix, not merely ask for an exception.

### 14.4 Vocabulary restrictions

Use these terms precisely:

- `execution correctness` for termination, endpoint count, and recovery
- `endpoint marginal bound` for one-card pushforward distance
- `coalition-view privacy` only for a theorem comparing coalition view
  distributions
- `trace privacy` only for a theorem about the chosen finite trace observation
- `end-to-end` only when the formal dependency chain reaches the named
  executed observation and the named security theorem

Use `distribution` for an `fdist` value in rendered source prose. Do not use
`law` as a prose synonym. Existing identifiers such as `sa_seat_dist_law` and
historical file names are exempt from this vocabulary rule.

Do not call `ts_private` a distributional privacy theorem. It is an
alternative-sharing compatibility property.

## 15. Probe gate

Before writing an implementation plan, create permanent probe files under the
repository's established probe or scratch convention. Do not delete them.

At minimum, probe all of the following.

### 15.1 Profile split probe

Construct the revised probability-independent program profile and execution
plug for both PGL and five-card carriers.

Passing condition:

- the two executions elaborate without a `realType` parameter in the program
  layer
- the existing process lists are recovered by definitional equality or small
  transport lemmas
- den Boer and Kim program-level compatibility names reduce or prove equal to
  the same five-card core profile
- the before-and-after API table accounts for every explicit `exec_*` and
  `sa_*` application whose argument list changes

Mutation check:

- replace the five-card reconstruction plug with the PGL plug and confirm that
  the construction fails by type mismatch

### 15.2 Field-removal probe

Construct both execution plugs without `ep_cards_bridge`. Construct one
`ShuffleMarginalBound` with no optional certificate, one exact bundle, one
asymptotic bundle, and Kim's bundle with both attachments.

Passing condition:

- all current live constructors have a migration path
- no public theorem statement must be weakened
- all direct `MkSecurityWitness` sites are assigned to a target constructor in
  the Section 5.3 matrix
- `AlgebraicRigidity` and `CombinatorialRigidity` elaborate with the bundle
  layer, while `SecurityProfile` and `CertifiedSolution` elaborate with the
  bound layer
- `profile_eps_pgl27`, `den_boer_perfect`, `pgl27_sample_cut_distE`,
  `den_boer_witness_rotationE`, and `den_boer_sample_cut_witnessE` elaborate
  against separate bound values rather than `mp_security`

Mutation checks:

- attach a `SecurityExact` built for a different distribution and confirm that
  the exact bundle construction fails
- prove projection equations showing that each existing exact or asymptotic
  producer remains attached to its migrated bundle, then replace one
  attachment by `None` in a mutation and confirm that its equation fails

### 15.3 Computational-cache probe

Re-run the concrete player-list and direct-enumeration reductions. Record the
commands, elapsed times, and normal-form behavior.

Passing condition:

- `ep_players` and `ep_playersE` remain justified by a reproducible reduction
  difference

If the current Rocq version has removed that difference, report it. Do not
remove the fields without a separate design update.

### 15.4 Outer-package probe

Construct one `ObservedExecution` for PGL and one for five-card. Derive
termination, endpoint count, and recovery solely through the generic exported
theorems.

Also specialize every raw-row extractor. Do not prove a semantic raw-trace
equation from the `ObservedExecution` fields.

Mutation check:

- remove the endpoint equation and confirm that recovery no longer follows

Scope check:

- enumerate the derived declarations and confirm that none states a semantic
  raw-row-to-content equality without an instance hypothesis

### 15.5 Sample and bridge probes

At the concrete carriers, elaborate:

- the PGL exact and word sample models
- both fixed-secret PGL models
- the den Boer uniform sample model
- the Kim symbolic biased sample model
- the Kim symbolic repeated sample model
- the Kim seven-cut sample model

First recheck the landed cut, coalition, joint, input-row, dealer-row, and
witness-tie declarations listed in Section 3. Use them as regression targets.
Then prove miniature equalities only for the still-missing models and between
their executed observations and the existing static security views.

The probe must include both typed observer bridges:

- the PGL finite content reader from generic participant rows to
  `pgl27_coalition_trace`
- `five_card_exec_colour_view A` to `ViewA R A` and `kim_view A`

For the five-card reader, instantiate `A` with an ordered sequence containing a
duplicate and with a sequence containing an out-of-range index. Confirm that
order, duplicates, and the `false` default agree. Check both possible rotation
orientations and retain only the compiled one.

Mutation checks:

- change the bias in the sample distribution without changing the claimed
  static distribution
  and confirm that the equality fails
- replace `word_eval` by a constant cut and confirm that the
  word-distribution bridge fails
- replace the five-card Boolean decoder by a constant function and confirm
  that the `kim_view` equality fails
- omit the extra small-bias hypothesis and confirm that the
  `kim_input_private` bridge cannot be instantiated

### 15.6 Generic transfer probe

Prove the exact `delta + delta` statement from Section 12 on a small concrete
finite carrier. Then instantiate its statement at the PGL types and rewrite
the PGL constant to `2^-39`.

Mutation check:

- remove the ideal view-distribution equality and confirm that the conclusion
  is not derivable from the remaining assumptions

Every probe result must have zero `Admitted`, `Abort`, or new `Axiom`. Report
`Print Assumptions` for each public probe theorem.

### 15.7 Hypothesis and vacuity probe

Instantiate the single-biased adapter hypotheses, the extra input-privacy
hypothesis, and the repeated spectral hypothesis at both bias zero and bias
`1/100` in a concrete real instance. This confirms that each hypothesis set is
jointly satisfiable and records which theorem consumes which assumption.

### 15.8 Facade and manifest probe

Create provisional PGL and five-card facades in permanent probe files before
fixing the public filenames. Import only the proposed manifest from a clean
client and check every alias listed in its table.

The probe must establish:

- that the seven-section facade order can be used without dependency cycles
- that profile, execution, observed-execution, and sample aliases retain their
  dependent indices
- that proof aliases retain the exact theorem assumptions and conclusions
- that an endpoint marginal bound cannot satisfy the witness required for a
  `Security-bridged` path
- that deleting or changing any listed alias makes the manifest checker fail
- that the H2 inventory finds every live `MonodromyProfile` constructor

Generate the H2 inventory by a reproducible repository search. Manually
classify false positives such as local probes, aliases, and commented examples.
The probe report must give the final facade basenames, import edges, public
aliases, completion levels, and theorem capabilities.

## 16. Required adversarial audits

Before implementation planning, run two independent audits.

### 16.1 Soundness audit

The auditor must check:

- that the revised package does not infer security from execution correctness
- that each sample distribution is the distribution named in its theorem
- that PGL constants remain `2^-40` and `2^-39` in full `L1` distance
- that the Kim seven-cut result remains endpoint-level
- that the biased single-cut mutual-information theorem uses the intended
  biased sample distribution
- that no field removal silently drops a theorem assumption
- that no exact or asymptotic certificate producer loses its attachment
- that a participant-coalition claim does not silently include the dealer or
  an input party
- that the input-row constant-conditioning equality is not reported as input
  privacy
- that the five-card decoded sequence reader has the same order, duplicate,
  orientation, and out-of-range behavior as `kim_view`
- that every manifest completion level is justified by the typed witnesses in
  its row
- that no endpoint marginal bound is classified as a security bridge
- that every manifest security capability names its exact distribution,
  observer, and security notion
- that each `NEEDS-PROBE` statement matches the theorem described in prose

The verdict must be GO or NO-GO with evidence for every finding.

### 16.2 API and naming audit

The auditor must check:

- MathComp naming and suffix conventions
- whether the proposed outer-package name collides with an existing type
- whether a field is duplicated by an existing projection
- whether every retained non-obvious field has the required comment
- whether compatibility aliases are sufficient for current clients
- whether the Section 5.3 matrix covers every affected file and direct old
  constructor site
- whether every removed explicit `R` argument has a before-and-after API entry
- whether the fixed record skeletons elaborate without duplicating parameters
- whether the two facades follow the same seven-section order and expose one
  stable public route to every featured analysis path
- whether the manifest imports introduce a dependency cycle or duplicate a
  proof body
- whether every manifest identifier resolves and the H2 inventory covers every
  live profile constructor

The verdict must be GO or NO-GO with a concrete migration table.

Fold all accepted findings back into this request before writing an
implementation plan.

### 16.3 Fold-back record and required re-audit

Two independent read-only audits of the previous revision returned NO-GO on
2026-08-12. This revision accepts their blocking findings as follows:

| Finding | Resolution in this revision |
|---|---|
| `SecurityWitness` affects a repository-wide client graph. | Section 5.3 requires a complete migration matrix. |
| A type alias cannot preserve `MkSecurityWitness` arity. | Section 5.2 fixes an atomic two-record migration and an explicit compatibility rule. |
| Exact and asymptotic producer capability would be lost. | Sections 5.2, 6.1, and 6.2 preserve both attachments in `ShuffleCertificateBundle`. |
| Removing `R` leaves phantom program parameters and many explicit applications. | Section 5.1 fixes one five-card core profile and requires a signature table. |
| `ObservedExecution` had no exact dependent shape. | Section 9 gives a self-contained record skeleton. |
| Raw trace semantics were incorrectly described as generic derivations. | Sections 7.8 and 9 separate extraction from instance semantic bridges. |
| Generic PGL raw traces do not have a finite distribution carrier. | Section 10.1 requires a finite content reader and a probe. |
| The generic five-card coalition view and `kim_view` have different types. | Section 10.2 defines a sequence-indexed decoded colour reader and a probe. |
| The Kim privacy theorem needs a stronger small-bias hypothesis. | Section 10.2 assigns hypotheses to the precise adapter or bridge that consumes them. |
| The generic transfer theorem was under-specified. | Section 12 pins all carriers, distributions, maps, and assumptions. |
| Verifier and out-of-range input rows were not represented precisely. | Section 7.8 adds a verifier extractor and separates valid input indices from defaults. |
| `sa_joint_dist` was described more strongly than its type. | Section 7.5 now says finite-valued sample observable. |

After the Section 15 probes compile, run the two audits again on this revision
and the permanent probe files. An implementation plan is forbidden until both
return `VERDICT: GO`.

The Section 13 facade and manifest design was added after the earlier audits.
The required re-audit must therefore treat the whole of Section 13 as new
scope, rather than assuming that the earlier findings cover it.

### 16.4 Probe-round and re-audit record (2026-08-12, HEAD 995e2a39)

The Section 15 probe gate compiled in full: units A (15.1+15.3), B (15.2),
C (15.4), D1 (five-card 15.5 + 15.7), D2 (PGL 15.5), E (15.6), F (15.8) —
17 permanent probe files under
`docs/superpowers/probes/2026-08-12-layered-protocol-packing/`, zero
`Admitted`/`Abort`/`Axiom`, every public probe result `Qed` with
`Print Assumptions` at the boolp trio or fully closed, every Section 15
mutation check red with harvested errors. Evidence index: `probe-ledger.md`
in that directory.

Both required audits were then re-run on this revision plus the probes.
Soundness audit: `VERDICT: GO`. API and naming audit: `VERDICT: GO`.
Accepted findings, folded into this request as amendments:

1. (Soundness 9-12, MAJOR, Section 13.) The production manifest must compute
   each completion level cumulatively from the typed witnesses present in
   that row and never assign a level above the highest witnessed one; each
   facade must alias the distribution-to-observer bridge lemmas its rows
   depend on (the probe-compiled `*_cut_distE` / `*_coalition_distE` /
   `*_content_trace_distE` family); capabilities are recorded one line per
   (theorem, distribution, observer, security notion) tuple; the PGL facade
   must expose the executed content reader and the executed 2^-39 bridges of
   probe unit D2, checked against the Section 13.1 minimum list.
2. (Naming 1-2, MAJOR.) Facade aliases use Module namespacing
   (`Module PGL27Analysis` / `Module FiveCardAnalysis`) instead of a flat
   `fa_` prefix, which trips I001 on 26 names; the four long production
   names (`five_card_exec_colour_view`, `five_card_colour_view_leak_bound`,
   `pgl27_exec_exact_view_indep`, the five-card observed-execution recon
   discharge) carry substantive `Naming:` lines.
3. (Naming 3-4, MAJOR.) The Section 5.3 matrix gains rows for the five
   `profile_k_*` lemmas (statements lose `R`) and for
   `instances/pgl27/pgl27_run.v` (`run_recover_pgl27`, `run_party_pgl27`).
4. (Naming 5, MAJOR.) The manifest cannot live directly under
   `pgg-smc/instances/` (no `-R` mapping exists for that parent and adding
   one would double-map every subdirectory). It lives in a new root,
   `pgg-smc/manifest/pgg_analysis_manifest.v`, with one new
   `-R pgg-smc/manifest pgg_smc` line and ordered `_CoqProject` entries.
5. (Soundness 19 / probe B.) The Section 5.2 record shapes require, verbatim:
   `Arguments MkShuffleMarginalBound {R M} _ _ _ _.`,
   `Arguments MkShuffleCertificateBundle {R M} _ _ _.`, and
   `clear implicits` on both records. The Section 9 record lives inside a
   module with `Unset Implicit Arguments` (probe C).
6. (Soundness 16.) Section 12's "bind explicitly" is satisfied in the
   statement; the production lemma additionally carries
   `Arguments var_dist_fdistmap_transfer : clear implicits.` Its production
   home is `pgg-smc/security/pgg_collusion_bound.v` (which already owns
   `var_dist_triangle` and `var_dist_fdistmap`), together with the new
   `var_dist_refl`.
7. (Naming 9.) `bound_of_witness` / `bundle_of_witness` are probe scaffolding
   and do not ship; the atomic migration constructs bounds and bundles
   directly.
8. (Naming 10-11.) Facade aliases target post-migration names only;
   `pgl27_certificate_bundle` replaces the draft name `pgl27_security_bundle`
   (head-noun conformance with `ShuffleCertificateBundle`).
9. (Naming 12.) Section 14.2's mandatory list gains `mp_M`, `mp_PI`, and
   `mp_plug`; the `sw_L` consumer list moves to the module overview comment,
   keeping the field comment declarative.
10. (Naming 20.) Section 13.4 correction: OC has no `MonodromyProfile`; the
    remaining-instance inventory lists it as not facade-eligible (with
    monster, cyclic, star), not as a remaining profile instance.
11. (Soundness 14 sub-finding.) The decoded sequence reader's `A` is a list
    of seat indices into the endpoint list; comments say so rather than
    "card positions".
12. (Soundness 18 / probe D1.) The Kim bridge's hypothesis set is confirmed:
    `kim_input_private` consumes `eps_lt_inv5`, `eps_gt_neg4inv5`, and the
    Section 10.2 small-bias hypothesis `eps_small : 0 < 5^-1 - |eps|`
    (kim_input_privacy.v:420). After stage A the executed bridge's
    discharged signature must reduce to exactly these three.
13. (Counting corrections.) The producer tally in the inventory is stated as
    an enumerated list rather than "19"; the H2 grep returns 22 hits;
    the five-card facade observer block enumerates five carriers.

## 17. Claim ledger

| Claim | Current evidence | Passing condition |
|---|---|---|
| The same five-card process supports several biases and lengths. | `five_card_exec_procs_biasE`. | One probability-independent five-card program profile and execution plug. |
| PGL exact and word analyses use one executable program. | `pgl27_exec_plug`, `pgl27_sample`, `pgl27_word_sample`. | Both models refer to the same revised `(mp, e)` pair. |
| Program packing does not need one security witness. | `five_card_exec_procs_biasE` shows that the process list ignores bias and length. Current profile-security consumers are accessors, distribution aliases, `profile_eps_pgl27`, `den_boer_perfect`, and the newly landed witness ties. | All program and execution definitions elaborate after its removal, and every landed equality is preserved through separate certificate values. |
| `sw_exact` and `sw_asymptotic` do not belong to the always-present marginal-bound record. | They have no projection consumers but have live producers in Kim, Schreier, S5, S5xS5, OC, and uniform security. | All producers migrate to `ShuffleCertificateBundle`, with no certificate data or theorem lost. |
| `ep_cards_bridge` supports no live client. | Only unused `exec_content_from_plug` consumes it. | Repeated audit plus successful PGL and five-card execution construction without it. |
| The concrete player list is a justified cache. | Earlier direct-enum reduction became stuck, while concrete lists reduced quickly. | Reproducible probe and a coherence theorem `ep_playersE`. |
| The outer package derives execution correctness. | Existing `exec_run_correct`, endpoint, and recovery theorems. | PGL and five-card packages derive the results without duplicate proof bodies. |
| Sample adapters reach static observations. | Existing `sa_seat_distE` and `sa_coalition_distE`. | Concrete equalities for every required model. |
| The PGL word sample has an explicit probability path to its cut and static coalition observation. | `pgl27_word_cut_distE`, `pgl27_word_sample_joint_distE`, and `pgl27_word_sample_coalition_distE`. | These results survive packing, then feed public bridges to the existing security theorems. |
| PGL finite-word privacy reaches executed observations. | Existing mixing, static view, and finite content-trace theorems are currently in separate files. | A probed finite reader and a public rewrite chain connect the word sample package to the existing `2^-39` result. |
| The uniform five-card cut matches the den Boer witness. | `five_card_sample_cut_distE`, `den_boer_witness_rotationE`, and `den_boer_sample_cut_witnessE`. | The equality survives removal of `mp_security` through a separate den Boer bound value. |
| Five-card observer rows have different meanings. | The two valid input rows are empty under sender logging, out-of-range rows use a default, and the decoded dealer row determines the input pair. | The outer package and bridge comments name the observer and preserve these cases without turning them into coalition privacy. |
| Five-card biased input privacy reaches the intended sample distribution. | `kim_input_private` is stated over `kim_input_dist`; generic coalition views have a different codomain. | A biased sample adapter, the small-bias hypothesis, and a probed decoded sequence reader equal to `kim_view`. |
| Exact-to-finite view transfer is reusable. | The proof shape exists inside `pgl27_word_view_indist`. | The pinned `delta + delta` theorem compiles and is instantiated by PGL. |
| The featured analyses have one public navigation route. | Their profiles, executions, observers, sample models, and theorems currently live across several files. | The manifest imports the two seven-section facades, every row resolves, and each completion level is backed by typed witnesses. |
| Partial instances remain visible without false completeness claims. | Live profile constructors have different execution, sampling, and theorem coverage. | The H2 inventory assigns each analysis path only its actual highest level and lists every missing layer. |

## 18. Soundness invariants

The completed work must satisfy all of these conditions.

1. Introduce no new `Axiom`, `Parameter`, `Admitted`, or `Abort` in permanent
   sources.
2. Do not change the mathematical statements or constants of existing PGL,
   den Boer, or Kim security theorems merely to fit the package.
3. Do not identify endpoint marginal mixing with coalition privacy.
4. Do not identify execution correctness with security.
5. Do not assign a finite distribution to a raw `seq` trace unless a finite
   trace observation has been defined.
6. Preserve the distinction between an arbitrary input prior, a uniform secret
   prior, and a fixed input.
7. Preserve every cut-membership hypothesis needed by reconstruction.
8. Preserve the full-`L1` convention used by `var_dist`.
9. Preserve the actual den Boer and Kim sample distributions. A profile name
   does not determine a probability distribution after `mp_security` is
   removed.
10. Preserve the concrete participant-list cache until the computational probe
    justifies a separate change.
11. Keep participant, input-party, dealer, verifier, and coalition
    observations distinct. No package name may erase the observer boundary.
12. Preserve the finite-reader parameter of `sa_joint_dist` unless a stronger
    type for `ep_inputT` is separately designed and probed.
13. Preserve every exact and asymptotic certificate currently constructed,
    even though the optional slots leave the marginal-bound record.
14. Keep the Kim sequence observer's order, duplicates, Boolean decoding, and
    out-of-range default behavior.
15. Keep the two weight-positivity hypotheses, the small-bias privacy
    hypothesis, and the spectral hypothesis distinct.
16. Do not broaden the request into a rewrite of `ReconPlug`, `PGGInterface`,
    covering schemes, or the piSMC interpreter.
17. Do not modify the WADT paper in this task.
18. Keep completion levels analysis-path-specific. One fully bridged model must
    not raise the reported level of another model for the same protocol.
19. Back every facade and manifest claim with a resolving typed alias. Do not
    use prose-only completion claims.
20. Preserve one explicit observer and theorem capability per manifest row.
    Do not replace them with an undifferentiated `secure` flag.
21. Keep facades proof-thin. They may re-export or alias public results but must
    not become a second home for copied proof bodies.

## 19. Non-goals

This request does not ask for:

- automatic privacy from every `MonodromyProfile`
- a single record containing every theorem about an instance
- seven-cut five-card coalition or trace privacy without a new proof
- raw-trace distributions over non-finite `seq` carriers
- active security, compositional security, or post-reveal security
- a new partial-erasure decoder or dropout-tolerance theorem
- removal of `rp_content`, `pi_starts_uniq`, `ep_players`, `ep_playersE`,
  `ep_players_bridge`, `ep_fuel`, or `sw_L`
- a single dependent record containing every facade component and theorem
- implementation of the Phase-H2 facades or missing proofs for non-featured
  instances in this request
- raising an instance's completion level by adding an unrequested theorem
- changes to the paper, bibliography, slides, or blueprint

## 20. Required completion report

The formalization tool must report:

1. A GO or NO-GO verdict for every required stage.
2. The final record and field tables.
3. Every removed field and the exact replacement path.
4. Every retained non-obvious field and the comment that documents its role.
5. The PGL and five-card package values that were constructed.
6. The exact bridge theorem from each package to each existing security result.
7. Probe paths, mutation-check results, build commands, and timings.
8. `Print Assumptions` output for new public theorems.
9. The list of files changed.
10. The exact build and audit commands used.
11. Any deferred field split and why it remained outside this request.
12. The migration status of every public and supporting declaration listed in
    Section 3.
13. An observer table separating participant, coalition, input-party, dealer,
    and verifier observations and the theorem available for each.
14. Any unused compatibility alias removed after a repeated usage audit.
15. The complete Section 5.3 migration matrix, including all direct old
    constructor sites and every changed explicit generic application.
16. The exact hypotheses consumed by each five-card sample model and bridge.
17. The compiled statement and mutation checks for each `NEEDS-PROBE` item.
18. The final PGL and five-card facade paths, seven-section inventories, and
    public alias types.
19. The complete repository manifest with one row per featured analysis path,
    including its observer, completion level, and exact theorem capability.
20. Evidence that every manifest row resolves from a clean client that imports
    only the manifest.
21. The Phase-H2 inventory of every remaining live profile, its existing typed
    witnesses, its actual highest level, its missing layers, and the proposed
    migration order.

The final report must state the strongest paper-facing claim that the completed
formalization supports. It must also list nearby claims that remain false.

## 21. Acceptance criterion

The request passes only if the final formalization supports this statement:

> One algebraic program profile and one execution plug determine the shared
> piSMC run and its executed observations. Several probability models can be
> attached to that same executable program. Explicit bridge theorems connect
> each featured model to its existing exact or finite-shuffle analysis. One
> typed manifest exposes the program, execution, observers, models,
> correctness results, security results, and transfer results for each
> featured analysis path without erasing their different types.

It must not require or imply this stronger statement:

> Filling one program profile automatically proves security for every shuffle
> distribution and observer.
