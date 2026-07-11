# PGL(2,7) orbit-class instance + transitivity-privacy bridge: design

Date: 2026-07-11
Status: approved design, revised after adversarial review (all 10 findings
applied; see section 9), ready for implementation planning.
Sources: `pgg-smc/notes/20260702-114631-pgl27-orbit-class-ROCQ-formalization-spec.md`
(design-validated spec, shape probe `.local/wip/pgl_shape_probe.v` compiled),
`pgg-smc/notes/20260701-175221-report-shuffle-matters-group-ladder.md` (research),
project memory `project_shuffle_matters_ladder`.

## 1. Goal

Formalize in Rocq, on branch `pgg-smc`:

1. A reusable framework bridge `pgg-smc/reconstruct/transitivity_privacy.v`:
   a shuffle group acting t-transitively on the N positions, with a deck
   multiset fixed across secrets, gives every coalition of size <= t a view
   distribution identical across secrets, discharging `ts_private`
   (Theorem B). Plus the monotone leakage ramp via the data processing
   inequality (Theorem A, non-gating tail).
2. A fifth PGG instance `pgg-smc/instances/pgl27/`: an 8-card scheme whose
   bool secret is the PGL(2,7) orbit-class (cross-ratio class) of the
   4-heart subset (orbits 42/28 of the 70 4-subsets), shuffled by one
   uniform draw from PGL(2,7), coalitions of size <= 3 private via sharp
   3-transitivity, reconstruction from the full revealed row.

Threshold convention (fixing all three numbers once): the record field is
`ts_k' = 3`; the derived framework threshold is `ts_k = ts_k'.+1 = 4`; the
private coalitions are those with `#|C| < ts_k'.+1`, i.e. `#|C| <= 3`
(pgg_sharing_framework.v:58,99-100).

Orbit terminology: the 42-orbit is the harmonic cross-ratio class
(values {2,4,6} in F_7), the 28-orbit the equianharmonic class ({3,5}).
Never call the 42-orbit "generic" (over F_7 every cross-ratio value is
harmonic or equianharmonic).

Security direction only. Non-goals (unchanged from the source spec):
no gray-zone (coalition size 4..6) leakage values, no AG-code or
covering-curve recovery (the Klein / Riemann-Hurwitz / `pgl_bound` role of
PGL is not used; a `CoveringScheme` is also type-impossible here since
`cs_plug` requires secretT = `'I_(pgg_N' M).+1`, not bool), no Mathieu rung
now (the bridge is written to accept it), no native modelling of the
"revealing N-1 cards determines the secret" refinement, no
SecurityAsymptotic / mixing file (single uniform draw; den Boer pattern).

## 2. Decisions locked in this brainstorm (2026-07-11)

| # | Decision | Detail |
|---|----------|--------|
| L1 | Scope expansion approved | pgl27 becomes the fifth in-scope instance (previously kim2025 / denboer1989 / s5 / s5x5). Update the `project_pgg_instance_scope` memory at completion. |
| L2 | Axiom policy: structural first, axiom fallback | Applies only to `pgl_3transitive` and `pgl27_card`. Bounded structural attempt (60-turn rocq-prover budget, then `rocq:autoprove` escalation); on non-convergence, a named justified computational axiom per the `s5_group_order_eq` precedent (rigidity_s5_instance.v:263), isolated in `pgl27_group.v`, reported at merge. |
| L3 | Theorem B has NO axiom fallback | It is the novel contribution; fallback is the combinatorial equal-support proof over the 70 4-subsets (subsets, not permutations, so no D6 conflict), not an axiom. |
| L4 | Theorem A is the final non-gating milestone | Proved last in `transitivity_privacy.v`; never blocks the instance critical path. Kept local (not upstreamed to infotheo), noted as upstreamable. |
| L5 | `rp_content` is probe-and-locked during plan writing | A rocq-prover probe typechecks both variants (colour folded into `orbit_class` with `rp_content = id` vs explicit face map) against the live `ReconPlug`; the implementation plan names the winner. Criterion: cheapest `orbit_recon_invariant`. |
| L6 | Execution strategy B: two-track parallel | User authorizes 2 concurrent rocqworkers for this build only, under the section 3 guardrails. |
| L7 | `ts_valid` carries the deck constraint, in Prop | `ts_valid s sh := deck_ok sh /\ orbit_class sh = s` where `deck_ok` states the fixed 4-hearts/4-clubs deck multiset. Required so Theorem B's `deck_ok` hypothesis and conclusion match the `ts_private` obligation (the probe's SHAPE C requires and returns `deck_ok`). `ts_correct` becomes a projection; `ts_encode_valid` additionally obliges `deck_ok (orbit_encode s)`. |
| L8 | Trace secrecy gets the s5 file split and an explicit probability model | An eighth file `pgl27_trace.v` mirrors `s5_trace.v`; `pgl27_secrecy.v` holds only view independence. The sampler fdist is named up front (section 4). |

The source note's section 5 record table remains normative except as
amended here (L7 `ts_valid`; `sw_L` and `sw_asymptotic` added;
`pi_starts_uniq` replacement; Prop not bool equalities). The note's locked
decisions D1..D8 carry over unchanged, notably: monodromy via
`@Gen_PGGTypes 2 6 pgl27_gens` with identity inclusion into S_8 (D1;
indices per pgg_interface.v:516-522 mean `m.+1 = 3` generators and
`n.+2 = 8` points, so `2 6` is correct for a `3.-tuple {perm 'I_8}`; the
probe's `@Gen_PGGTypes 1 6` was for its 2-generator abstraction); `pgl2`
from `pgl_bound.v` used only for the cardinality fact (D2); privacy witness
is re-dealing, not group-masking, because sharp 3-transitivity makes
3-point stabilisers trivial, so `rp_monodromy` powers correctness only
(D5); everything proved abstractly over the group, no `vm_compute` on
permutations (D6); `sw_bound_eps = 0` exact (D7); s5-style secret-sharing
family with empty input prologue (D8).

Probe caveat (do not copy): the probe ascribes `pgl_M : MonodromyReprType`,
which erases the HB generator structure that `MonodromyProfile.mp_M` and
`SecurityWitness` require (`MonodromyReprWithGeneratorType`,
pgg_monodromy_profile.v:51, algebraic_rigidity.v:82). `pgl27_group.v` must
leave `pgl_M := @Gen_PGGTypes 2 6 pgl27_gens` unascribed, as
`s5_profile.v:51-52` does.

## 3. Architecture: two-track execution

| Phase | Files | Agent | Depends on |
|-------|-------|-------|------------|
| Track 1 | `reconstruct/transitivity_privacy.v` (Theorem B only) | rocq-prover #1 | framework `.vo`s (already built) |
| Track 2 | `instances/pgl27/pgl27_group.v`, then `pgl27_orbit.v` | rocq-prover #2 | framework `.vo`s (already built) |
| Join (sequential) | `pgl27_scheme.v`, then `pgl27_profile.v` + `pgl27_run.v`, then `pgl27_secrecy.v`, then `pgl27_trace.v` | one agent | Tracks 1 and 2 complete |
| Tail (non-gating) | Theorem A appended to `transitivity_privacy.v` | one agent | join complete |

Concurrency guardrails:

- Maximum 2 rocqworkers alive at any moment (one per track), and at most
  ONE live `make` invocation across both tracks at any instant (a track
  wanting `make -j1` waits for the other's `make` to finish); proof
  iteration parallelism comes only from the two rocq-mcp sessions.
- Between-cycle `ps aux` memory checks; hard-interrupt and pause one track
  if the COMBINED rocqworker footprint exceeds ~14-16 GB (24 GB machine,
  headroom for the OS and editors).
- Both tracks share one worktree; their files are disjoint and both depend
  only on prebuilt framework `.vo`s.
- The join phase and tail drop back to a single worker.

## 4. Components and record wiring

New files (compile order): `transitivity_privacy` -> `pgl27_group` ->
`pgl27_orbit` -> `pgl27_scheme` -> `pgl27_profile` -> `pgl27_run` ->
`pgl27_secrecy` -> `pgl27_trace`. `_CoqProject` gets BOTH edits: the line
`-R pgg-smc/instances/pgl27 pgg_smc` AND the seven pgl27/bridge `.v`
entries appended to the file list (`transitivity_privacy.v` is covered by
the existing `-R pgg-smc/reconstruct pgg_reconstruct` mapping but still
needs its file-list entry).

Probability model (L8): the sampler space is the finite product of the
uniform draw `g` over `pgg_G pgl_M` (336 elements) with the dealt
arrangement; the secret RV is `orbit_class` of the dealt arrangement
(prior 42/70 vs 28/70, deliberately non-uniform; independence, not
uniformity, is what secrecy needs); the coalition view RV is the <= 3
revealed colours after applying g. The distributional corollary of
Theorem B (equal conditional view laws across secrets => view independent
of secret) is proved in `transitivity_privacy.v` alongside Theorem B and
consumed by `pgl27_secrecy.v`.

| File | Key contents |
|------|--------------|
| `reconstruct/transitivity_privacy.v` | Theorem B: t-transitive action + fixed deck => <= t coalition view secret-independent => `ts_private` (side-hypotheses: `Htrans`, `Hinv`, `Hdeck_stable`, `Hpopulated`, `#|C| < t.+1`; `deck_ok` flows through `ts_valid` per L7). Distributional corollary for view independence (L8). Theorem A (tail): `A \subset B -> mutual_info(Secret, View A) <= mutual_info(Secret, View B)` via infotheo `data_processing_inequality`. Group-agnostic. |
| `pgl27_group.v` | P^1(F_7) identification on `'I_8` (0..6 field elements, 7 = infinity); `pgl27_gens : 3.-tuple {perm 'I_8}` (z+1, 3z, -1/z; 3 is a non-square mod 7, which is what exceeds PSL); `pgl_M := @Gen_PGGTypes 2 6 pgl27_gens` (unascribed); `pgl27_card : #|pgg_G pgl_M| = 336`; `pgl_3transitive : ntransitive 3 (@pgg_rho pgl_M @* pgg_G pgl_M) [set: 'I_8] 'P`. |
| `pgl27_orbit.v` | `deck_ok` (fixed 4-hearts/4-clubs multiset predicate); `cross_ratio` (partial, total on distinct 4-tuples); `orbit_class : 8.-tuple 'I_8 -> bool` (true = 42-orbit / harmonic, false = 28-orbit / equianharmonic); `orbit_class_split` (42 and 28); `orbit_class_invariant` (PGL-invariance under the coordinate action); `orbit_encode` + `orbit_encodeK` + `orbit_encode_deck : deck_ok (orbit_encode s)`. |
| `pgl27_scheme.v` | `orbit_scheme : ThresholdScheme bool 'I_8` with `ts_T' = 7`, `ts_k' = 3`, `ts_valid s sh := deck_ok sh /\ orbit_class sh = s` (Prop, L7), `ts_recon = orbit_class`, `ts_encode = orbit_encode`, `ts_correct` by projection, `ts_encode_valid` from `orbit_encodeK` + `orbit_encode_deck`; `orbit_private` (Theorem B instantiated); `orbit_plug : ReconPlug pgl_M bool` with `rp_scheme = orbit_scheme`, `rp_content` per L5 probe, `rp_monodromy = fun g => @pgg_rho pgl_M g`, `rp_recon_invariant = orbit_recon_invariant` (from `orbit_class_invariant`). |
| `pgl27_profile.v` | `pgl27_PI : PGGInterface pgl_M` (`pi_T' = 7`, `pi_starts = ord_tuple 8`, `pi_starts_uniq` by a custom one-liner `pgl27_starts_uniq : uniq (ord_tuple 8)` mirroring `s5_starts_uniq` at s5_profile.v:30 — there is NO mathcomp lemma `ord_tuple_uniq`); `pgl27_security : SecurityWitness R pgl_M` with ALL SIX fields: `sw_L = 0`, `sw_bound_eps = 0`, `sw_rho_dist` = uniform on the pgg_rho image, `sw_bound` exact (uniform draw over a transitive group gives an exactly uniform single-card marginal, axiom-free), `sw_exact = Some ...` (`SecurityExact` per-s var_dist equality), `sw_asymptotic = None` (den Boer uniform-dealing pattern, algebraic_rigidity.v:102-104); `pgl27_profile : MonodromyProfile R` (mp_M = pgl_M, mp_secretT = bool, mp_PI, mp_security, mp_plug). |
| `pgl27_run.v` | The dealer-run pipeline mirroring `s5_run.v`'s full artifact set: `pgl27_players`, `pgl27_dealer_run`, `pgl27_procs`, `pgl27_run_terminates`, `pgl27_endpoints` + `pgl27_endpoints_size`, and the target `pgl27_run_recovers` (recon of the dealt-then-shuffled encoding returns the secret, via `orbit_recon_invariant` + `orbit_encodeK`). |
| `pgl27_secrecy.v` | `pgl27_view_indep`: the <= 3-coalition view RV is independent of the secret RV over the section 4 sampler fdist, via the distributional corollary of Theorem B (the additive-sharing lemma `additive_view_indep` at pgg_randomized_sharing.v:147 does NOT apply here — one uniform group draw, not additive sharing). |
| `pgl27_trace.v` | The trace apparatus mirroring `s5_trace.v`: `content_of`-style projection lemmas over the run, the sampler space, `pgl27_player_trace` + its evaluation lemma, share/trace independence, and `pgl27_trace_secrecy : H(secret | player_trace) = H(secret)` via `trace_secrecy_of_view` (pgg_trace_secrecy.v:38) fed by `pgl27_view_indep`. |

Anchor points in live code (all verified 2026-07-11 by the review agent):
`pgg-smc/protocol/pgg_interface.v:38,56,379,542` (`PGGTypes` /
`isMonodromyRepr` / `PGGInterface` / `Gen_PGGTypes`),
`pgg-smc/reconstruct/pgg_sharing_framework.v:47` (`ThresholdScheme`),
`pgg-smc/reconstruct/covering_scheme.v:117` (`ReconPlug`),
`pgg-smc/reconstruct/algebraic_rigidity.v:147` (`SecurityWitness`, six
fields, lines 147-157), `pgg-smc/protocol/pgg_monodromy_profile.v:50`
(`MonodromyProfile R`), `pgg-smc/security/pgg_trace_secrecy.v:38`
(`trace_secrecy_of_view`), infotheo `information_theory/entropy.v:1634`
(`data_processing_inequality`), mathcomp
`solvable/primitive_action.v:159` (`ntransitive`; `dtuple_on` at 158;
currently unused anywhere in pgg-smc).

## 5. Proof obligations, risks, and strategies

| Obligation | Risk | Primary strategy | Fallback |
|-----------|------|------------------|----------|
| Theorem B (bridge => `ts_private`) | HIGH | orbit-stabiliser => uniform t-tuple => hypergeometric marginal => equal support => re-dealing witness | combinatorial equal-support over the 70 subsets (no axiom, L3) |
| distributional corollary (view independence) | HIGH | equal conditional view laws across secrets => independence over the named fdist | conditional-law case split over bool secret |
| `pgl_3transitive` | HIGH | sharp 3-transitivity of Moebius maps on P^1(F_7) + `<<gens>> = PGL` via card 336 | justified computational axiom (L2) |
| `pgl27_card` = 336 | MED | `card_pgl2` bridge or generated-subgroup order | justified computational axiom (L2) |
| `orbit_class_invariant` | MED | cross-ratio is a PGL-invariant of 4-tuples | per-generator invariance check |
| `orbit_class` / `orbit_class_split` | MED | decidable cross-ratio predicate; orbit-stabiliser counts | finite decision |
| trace apparatus (`pgl27_trace.v`) | MED | mirror `s5_trace.v` (projection lemmas, sampler, trace RV) | scope `pgl27_trace_secrecy` to an abstract view RV and document the divergence from the s5 mirror |
| Theorem A (tail) | MED | DPI lifted to the RV/View level | conditioning-reduces-entropy route |
| assembly (scheme/plug/profile/run) | LOW | mirror s5 / den Boer | |
| `pgl27_security` (eps = 0) | LOW | transitive-uniform marginal | |

Naming discipline (load-bearing, from the literature audit): "t-transitive"
or "t-wise uniform" names the group; the colour distribution is "sampling
without replacement / hypergeometric marginal", never "t-wise uniform".
Do not phrase Theorem B as orbit-independent design incidence: the two
4-subset orbits are 3-(8,4,3) and 3-(8,4,2) designs; the truth is that the
<= t position-marginal of a fixed deck sees only colour counts. Orbit
classes are "harmonic" / "equianharmonic", never "generic".

Axiom hygiene: target boolp-only plus at most the two L2 justified axioms.
`rocq_assumptions` on `orbit_private`, `pgl27_run_recovers`,
`pgl27_trace_secrecy` at the final gate; report the axiom set at merge.

## 6. Verification, audit, and completion criteria

- Proof iteration through rocq-mcp (`rocq_start` / `rocq_check` /
  `rocq_step_multi`); `make -j1` only for dependency refreshes and the
  final full-chain build, mutex-serialized across tracks (section 3).
- Per-milestone checkpoint commits through the rocq-audit gate: H-series
  role tags (`@intent:` / `@composes:` / `@main <label>:`) on every
  declaration, I-series naming (no metaphor identifiers, canonical MathComp
  suffixes), terse declarative statement comments (strategy and risk notes
  stay in this spec and the plan, never in code comments).
- Records-parity check against the s5 sibling: every claimed property is a
  persisted record field with parity to the sibling instances; nothing
  load-bearing stays prose-only. Justified non-parity (by design): no
  mixing/SecurityAsymptotic file (uniform dealing) and no
  rigidity/CoveringScheme file (bool secret; Klein side is a non-goal).
- Test-material sources: the s5 instance files
  (`s5_profile.v`, `s5_run.v`, `s5_secrecy.v`, `s5_trace.v`) are the
  structural fixture (assembly shapes), the shape probe
  `.local/wip/pgl_shape_probe.v` is the typecheck fixture (minus the
  forbidden ascription, section 2), `.claude/audit/fixtures/` remains
  untouched.
- Done means: all eight files compile in dependency order via `make -j1`;
  every target lemma is Qed; the axiom report shows boolp plus at most the
  two justified group-computation axioms; the audit gate passes; Theorem A
  landed in the tail.

## 7. Milestones

1. Plan-writing probes (before implementation): L5 `rp_content`
   probe-and-lock; typecheck the L7 `ts_valid` shape and the L8 fdist
   skeleton against the live records.
2. Tracks 1 and 2 in parallel (Theorem B + distributional corollary |
   group then orbit), checkpoint commit per completed file.
3. Join: `pgl27_scheme.v` (instantiate Theorem B), then profile + run,
   then secrecy, then trace.
4. Tail: Theorem A.
5. Final gate: full-chain build, `rocq_assumptions` report, audit pass,
   `project_pgg_instance_scope` memory update, spec-note status update.

## 8. Governance

The two-rocqworker RAM authorization (L6) is scoped to this build only and
does not change the standing `make -j1` single-worker rule (which the
one-live-`make` mutex in section 3 preserves in spirit: never two
concurrent `make` processes). The instance scope memory update (L1)
happens at completion, not before.

## 9. Revision log

2026-07-11, after adversarial review (agent run, 10 findings, all applied):
[ERROR] `ts_valid` now carries `deck_ok` in Prop (L7); [ERROR] probability
model + `pgl27_trace.v` file added (L8); [HIGH] `SecurityWitness` completed
to six fields with `sw_L = 0`, `sw_asymptotic = None`, types written as
`SecurityWitness R pgl_M` / `MonodromyProfile R`; [HIGH] probe's
`: MonodromyReprType` ascription forbidden; [MED] `ts_valid` reverted to
Prop equality; [MED] `pgl27_run.v` scoped to the full s5_run artifact set;
[MED] one-live-`make` mutex + combined 14-16 GB RAM threshold; [LOW]
`_CoqProject` file-list entries added; [LOW] `ord_tuple_uniq` (nonexistent)
replaced by a custom uniq lemma and the dropped record-table rows restored;
[LOW] k/k' threshold convention sentence added.
