# PGL(2,7) orbit-class instance + transitivity-privacy bridge: design

Date: 2026-07-11
Status: approved design, ready for implementation planning.
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
   uniform draw from PGL(2,7), privacy threshold k = 3 from sharp
   3-transitivity, reconstruction from the full revealed row.

Security direction only. Non-goals (unchanged from the source spec):
no gray-zone (coalition size 4..6) leakage values, no AG-code or
covering-curve recovery (the Klein / Riemann-Hurwitz / `pgl_bound` role of
PGL is not used), no Mathieu rung now (the bridge is written to accept it),
no native modelling of the "revealing N-1 cards determines the secret"
refinement.

## 2. Decisions locked in this brainstorm (2026-07-11)

| # | Decision | Detail |
|---|----------|--------|
| L1 | Scope expansion approved | pgl27 becomes the fifth in-scope instance (previously kim2025 / denboer1989 / s5 / s5x5). Update the `project_pgg_instance_scope` memory at completion. |
| L2 | Axiom policy: structural first, axiom fallback | Applies only to `pgl_3transitive` and `pgl27_card`. Bounded structural attempt (60-turn rocq-prover budget, then `rocq:autoprove` escalation); on non-convergence, a named justified computational axiom per the `s5_group_order_eq` precedent, isolated in `pgl27_group.v`, reported at merge. |
| L3 | Theorem B has NO axiom fallback | It is the novel contribution; fallback is the combinatorial equal-support proof over the 70 subsets, not an axiom. |
| L4 | Theorem A is the final non-gating milestone | Proved last in `transitivity_privacy.v`; never blocks the instance critical path. Kept local (not upstreamed to infotheo), noted as upstreamable. |
| L5 | `rp_content` is probe-and-locked during plan writing | A rocq-prover probe typechecks both variants (colour folded into `orbit_class` with `rp_content = id` vs explicit face map) against the live `ReconPlug`; the implementation plan names the winner. Criterion: cheapest `orbit_recon_invariant`. |
| L6 | Execution strategy B: two-track parallel | User authorizes exactly 2 concurrent rocqworkers for this build only. |

The source spec's locked decisions D1..D8 carry over unchanged, notably:
monodromy via `@Gen_PGGTypes 2 6 pgl27_gens` with identity inclusion into
S_8 (D1); `pgl2` from `pgl_bound.v` used only for the cardinality fact (D2);
privacy witness is re-dealing, not group-masking, because sharp
3-transitivity makes 3-point stabilisers trivial, so `rp_monodromy` powers
correctness only (D5); everything proved abstractly over the group, no
`vm_compute` on permutations (D6); `sw_bound_eps = 0` exact (D7);
s5-style secret-sharing family with empty input prologue (D8).

## 3. Architecture: two-track execution

| Phase | Files | Agent | Depends on |
|-------|-------|-------|------------|
| Track 1 | `reconstruct/transitivity_privacy.v` (Theorem B only) | rocq-prover #1 | framework `.vo`s (already built) |
| Track 2 | `instances/pgl27/pgl27_group.v`, then `pgl27_orbit.v` | rocq-prover #2 | framework `.vo`s (already built) |
| Join (sequential) | `pgl27_scheme.v`, then `pgl27_profile.v` + `pgl27_run.v`, then `pgl27_secrecy.v` | one agent | Tracks 1 and 2 complete |
| Tail (non-gating) | Theorem A appended to `transitivity_privacy.v` | one agent | join complete |

Concurrency rules:

- Maximum 2 rocqworkers alive at any moment (one per track); each track uses
  rocq-mcp for proof iteration and `make -j1` for its own compiles.
- Between-cycle `ps aux` memory checks; if any rocqworker exceeds ~10 GB,
  hard-interrupt and pause one track until the other's compile finishes.
- Both tracks share one worktree; their files are disjoint and both depend
  only on prebuilt framework `.vo`s, so no build-graph interference.
- The join phase and tail drop back to a single worker.

## 4. Components and record wiring

New files (compile order): `transitivity_privacy` -> `pgl27_group` ->
`pgl27_orbit` -> `pgl27_scheme` -> `pgl27_profile` -> `pgl27_run` ->
`pgl27_secrecy`. `_CoqProject` gains `-R pgg-smc/instances/pgl27 pgg_smc`.

| File | Key contents |
|------|--------------|
| `reconstruct/transitivity_privacy.v` | Theorem B: t-transitive action + fixed deck => <= t coalition view secret-independent => `ts_private` (side-hypotheses: `Htrans`, `Hinv`, `Hdeck_stable`, `Hpopulated`, `#|C| < t.+1`). Theorem A (tail): `A \subset B -> mutual_info(Secret, View A) <= mutual_info(Secret, View B)` via infotheo `data_processing_inequality`. Group-agnostic. |
| `pgl27_group.v` | P^1(F_7) identification on `'I_8` (0..6 field elements, 7 = infinity); `pgl27_gens : 3.-tuple {perm 'I_8}` (z+1, 3z, -1/z; the non-square scaling is what exceeds PSL); `pgl_M := @Gen_PGGTypes 2 6 pgl27_gens`; `pgl27_card : #|pgg_G pgl_M| = 336`; `pgl_3transitive : ntransitive 3 (@pgg_rho pgl_M @* pgg_G pgl_M) [set: 'I_8] 'P`. |
| `pgl27_orbit.v` | `cross_ratio` (partial, total on distinct 4-tuples); `orbit_class : 8.-tuple 'I_8 -> bool` (true = 42-orbit, false = 28-orbit); `orbit_class_split` (42 and 28); `orbit_class_invariant` (PGL-invariance under the coordinate action); `orbit_encode` + `orbit_encodeK`. |
| `pgl27_scheme.v` | `orbit_scheme : ThresholdScheme bool 'I_8` with `ts_T' = 7`, `ts_k' = 3`, `ts_valid s sh = (orbit_class sh == s)`, `ts_recon = orbit_class`, `ts_encode = orbit_encode`; `orbit_private` (Theorem B instantiated); `orbit_plug : ReconPlug pgl_M bool` with the L5 probe-locked `rp_content`; `orbit_recon_invariant`. |
| `pgl27_profile.v` | `pgl27_PI : PGGInterface pgl_M` (`pi_T' = 7`, `pi_starts = ord_tuple 8`); `pgl27_security : SecurityWitness` (`sw_bound_eps = 0`, `sw_exact` populated: uniform draw over a transitive group gives an exactly uniform single-card marginal, axiom-free); `pgl27_profile : MonodromyProfile` (mp_secretT = bool). |
| `pgl27_run.v` | `pgl27_run_recovers`: recon of the dealt-then-shuffled encoding returns the secret, via `orbit_recon_invariant` + `orbit_encodeK`, mirroring `s5_run_recovers`. |
| `pgl27_secrecy.v` | `pgl27_view_indep` (from Theorem B); `pgl27_trace_secrecy : H(secret | player_trace) = H(secret)` via `trace_secrecy_of_view`, mirroring `s5_trace_secrecy`. |

Anchor points in live code: `pgg_interface.v:38,56,379,542`
(`PGGTypes` / `isMonodromyRepr` / `PGGInterface` / `Gen_PGGTypes`),
`pgg_sharing_framework.v:47` (`ThresholdScheme`), `covering_scheme.v:117`
(`ReconPlug`), `algebraic_rigidity.v:147` (`SecurityWitness`),
`pgg_monodromy_profile.v:50` (`MonodromyProfile`),
`pgg_trace_secrecy.v:38` (`trace_secrecy_of_view`), infotheo
`information_theory/entropy.v:1634` (`data_processing_inequality`),
mathcomp `solvable/primitive_action.v:159` (`ntransitive` / `dtuple_on`,
currently unused anywhere in pgg-smc). Line numbers are as of the
2026-07-02 probe; re-verify during plan writing.

## 5. Proof obligations, risks, and strategies

| Obligation | Risk | Primary strategy | Fallback |
|-----------|------|------------------|----------|
| Theorem B (bridge => `ts_private`) | HIGH | orbit-stabiliser => uniform t-tuple => hypergeometric marginal => equal support => re-dealing witness | combinatorial equal-support over the 70 subsets (no axiom, L3) |
| `pgl_3transitive` | HIGH | sharp 3-transitivity of Moebius maps on P^1(F_7) + `<<gens>> = PGL` via card 336 | justified computational axiom (L2) |
| `pgl27_card` = 336 | MED | `card_pgl2` bridge or generated-subgroup order | justified computational axiom (L2) |
| `orbit_class_invariant` | MED | cross-ratio is a PGL-invariant of 4-tuples | per-generator invariance check |
| `orbit_class` / `orbit_class_split` | MED | decidable cross-ratio predicate; orbit-stabiliser counts | finite decision |
| Theorem A (tail) | MED | DPI lifted to the RV/View level | conditioning-reduces-entropy route |
| assembly (scheme/plug/profile/run/secrecy) | LOW | mirror s5 / den Boer | |
| `pgl27_security` (eps = 0) | LOW | transitive-uniform marginal | |

Naming discipline (load-bearing, from the literature audit): "t-transitive"
or "t-wise uniform" names the group; the colour distribution is "sampling
without replacement / hypergeometric marginal", never "t-wise uniform".
Do not phrase Theorem B as orbit-independent design incidence: the two
4-subset orbits are 3-(8,4,3) and 3-(8,4,2) designs; the truth is that the
<= t position-marginal of a fixed deck sees only colour counts.

Axiom hygiene: target boolp-only plus at most the two L2 justified axioms.
`rocq_assumptions` on `orbit_private`, `pgl27_run_recovers`,
`pgl27_trace_secrecy` at the final gate; report the axiom set at merge.

## 6. Verification, audit, and completion criteria

- Proof iteration through rocq-mcp (`rocq_start` / `rocq_check` /
  `rocq_step_multi`); `make -j1` only for dependency refreshes and the
  final full-chain build.
- Per-milestone checkpoint commits through the rocq-audit gate: H-series
  role tags (`@intent:` / `@composes:` / `@main <label>:`) on every
  declaration, I-series naming (no metaphor identifiers, canonical MathComp
  suffixes), terse declarative statement comments (strategy and risk notes
  stay in this spec and the plan, never in code comments).
- Records-parity check against the s5 sibling: every claimed property is a
  persisted record field with parity to the sibling instances; nothing
  load-bearing stays prose-only.
- Test-material sources: the s5 instance files are the structural fixture
  (assembly shapes), the shape probe `.local/wip/pgl_shape_probe.v` is the
  typecheck fixture, `.claude/audit/fixtures/` remains untouched.
- Done means: all seven files compile in dependency order via `make -j1`;
  every target lemma is Qed; the axiom report shows boolp plus at most the
  two justified group-computation axioms; the audit gate passes; Theorem A
  landed in the tail.

## 7. Milestones

1. Plan-writing probes (before implementation): re-verify the section 4
   anchor line numbers; L5 `rp_content` probe-and-lock.
2. Tracks 1 and 2 in parallel (Theorem B | group then orbit), checkpoint
   commit per completed file.
3. Join: `pgl27_scheme.v` (instantiate Theorem B), then profile + run,
   then secrecy.
4. Tail: Theorem A.
5. Final gate: full-chain build, `rocq_assumptions` report, audit pass,
   `project_pgg_instance_scope` memory update, spec-note status update.

## 8. Governance

The two-rocqworker RAM authorization (L6) is scoped to this build only and
does not change the standing `make -j1` single-worker rule. The instance
scope memory update (L1) happens at completion, not before.
