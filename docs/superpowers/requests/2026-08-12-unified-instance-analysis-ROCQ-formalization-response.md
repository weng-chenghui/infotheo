# Formalization response: unified analysis pipelines for all protocol instances

Date: 2026-08-12/13. STATUS: COMPLETE. All phases implemented and verified.
Baseline `5453b93b`, final commit `58a049c0`, 22 commits, every one through
the rocq-audit gate unbypassed with a compensating direct rocq-auditor
review (the gate's Stage 2 is a pre-existing S998 no-op). The §15 completion
report is at the end of this document.

## Implementation log

- T0 (`866275a9`): NEW `pgg-smc/manifest/pgg_analysis_status.v` (typed
  CompletionLevel/TransferStatus/PggAxiom/AssumptionStatus, no pgg imports);
  `var_dist_fdistmap_inj` relocated s5x5_mixing.v -> pgg_collusion_bound.v
  Section 1b, discharged signature byte-identical
  (`Arguments [R A B] [f] P Q _`), boolp-trio only; _CoqProject +1. Cone
  green (6 min serial). Gate passed; Stage 2 is a silent S998 no-op
  (schema breakage) — every commit gets a compensating direct rocq-auditor
  review as a result.
- Phase 1 S5 (T1.1 `26e49487` s5_exec.v 737 lines; T1.2 `1ec2b94e`
  s5_models.v 346; T1.3 `50daffad` s5_analysis.v 434): both plugs, both OE
  values, both adapters, executed trace+coalition secrecy, conditional word
  endpoint bound, Module S5Analysis with 38 aliases across the seven
  sections + bound sub-block, typed transfer statuses pinned by erefl
  retention checks. Print Assumptions exactly as the probe ledger predicted
  (ORDER = s5_group_order_eq on everything profile-touching; RAYLEIGH only on
  word_endpoint_bound; BOOLP on funext users). Zero name collisions with the
  landed s5 files. Deviations (all documented in the agent report and
  reflected in the facade): pgl27-parity recovery triple, E-suffix renames,
  verifier endpoints in section 3, model equations in section 4,
  transfer-status retention checks as erefl value pins, profile_k comment
  corrected to privacy threshold. Convention adopted for all facades: header
  sentence stating `exec_` = executed observer vocabulary, deterministic =
  unprefixed, randomized = `rand_` prefix.
- Phase 2 S5xS5 (T2.1 `2a103037` s5x5_exec.v 1054 lines; T2.2 `758b2cde`
  s5x5_models.v 895; T2.3 `351060ba` s5x5_analysis.v 606; comment
  remediation `d78fa6f2`): both plugs, product-tape recovery
  `s5x5_rfree_recon` KERNEL-CLOSED, executed trace/p1/p2/joint secrecy (new
  Pprod statements against JointSecret per O1), three conditional word
  bounds, two NegativeTransfer floors AND the L >= 17 positivity corollary
  `word_pile1_floor_gt0`/`pile2` (numeric route: round-at-1000 squaring
  chain, no lia, `s5x5_lazy_bound_lt1` boolp-only), Module S5x5Analysis with
  61 aliases; pile structure confirmed in every public type (per-pile
  {set 'I_5} coalitions, no flat {set 'I_10}). RAYLEIGH reaches seven
  results (five spectral + the two _gt0 corollaries). Deviations recorded:
  vm_compute on closed nat-arithmetic leaves (not run tables — safe),
  remediation as follow-up commit, s5x5_word_cut_imageE not ported (S5
  parity gap, two-line addition if wanted).
- Phase 3 Abelian (T3.1 `08684f4a` abel_profile.v revised in place +239/-6;
  T3.2 `566613cd` abelian_exec.v 582 lines; T3.3 `56b388f6`
  abelian_models.v 623; T3.4 `0b3b1574` abelian_analysis.v 374; audit fixes
  `6d0a4495`/`ddf91838`/`fc8360a9`): four-seat `abel_PI` (old
  `Gen_PGG_2 abel_sigmas` interface demoted to group-level prose; zero
  consumers migrated — genuine near-orphan; profile_k_abel unchanged by []),
  Klein facts in abel_profile.v, both plugs at fuel 150, constant recovery
  `Ordinal 2`, globally injective endpoint-vector observer, negative theorem
  chain (group form = executed form = 1 at every positive length; length-0
  witness 3/2), Module AbelianAnalysis. Print Assumptions over all 81 public
  values: 61 kernel-closed, 20 boolp-trio-only — NOTHING touches
  s5_rayleigh_Q2_R or any group-order axiom. Tag decision (flagged for
  T4.1): limitation theorems keep `@main security` per request §11; manifest
  capability text keeps the narrow labels (fixed-length mixing limitation,
  negative mixing result).
- Phase 4 repo contract (T4.1 `32b8ca82` manifest +1799/-40; T4.2
  `149e58ff` client +155/-12 + additive status aliases in
  five_card_analysis.v and pgl27_analysis.v; T4.3 `06ad3fea` + hardened
  `8393e5f9` profile_facade_check.sh with an 18-case regression suite;
  review fixes `531a4c40`, `58a049c0`): `AnalysisPathRow` record + 17 typed
  rows (matrix held exactly; two honest sample-slot deviations:
  pgl27_row_word None because its adapters are secret-parameterized;
  five_card_row_biased uses single_biased_sample at bias 1/100, not the
  seven-cut centi model), 218 aliases pinned by spelled type + 51 erefl
  status pins, mutation-tested; client reaches every section of all five
  facades + vocabulary + rows through exactly one Require; completeness
  check exit 0 with the pinned six-profile classification. "Absent
  capabilities" appendix names the S5/S5xS5 missing premises exactly and
  notes their group-uniform unsatisfiability (sign-coset confinement,
  marked not-formalized at S5/S5xS5).

## §15 Completion report

1. Verdicts: Phase 0 GO; S5 GO, S5xS5 GO, Abelian GO (all implemented).
   Both §18 re-audits GO.
2. Baseline `5453b93bb07b5eee63c331d17a9b95b62802b9d5`; final
   `58a049c088995cb35b0c4408f84c0c3b30eb190f`.
3. Declarations reused: S5 — s5_profile, profile_k_s5, s5_scheme,
   s5_run.s5_players, s5_procs, fuel 150, s5_run_terminates, s5_endpoints,
   s5_endpoints_size, s5_run_recovers, s5_verifier_endpoints (generic),
   s5_aprocs_abs, s5_rs, s5_rlayout, s5_rprocs, s5_player_trace,
   s5_player_trace_E, s5_share_indep, s5_trace_secrecy,
   s5_view_secrecy_concrete, s5_spectral_convergence_proved/gap,
   rho_from_words, path_gen_tuple, trace_secrecy_of_view,
   leakage_of_view_indep, var_dist_fdistmap_transfer. S5xS5 — s5x5_profile,
   profile_k_s5x5, s5x5_scheme, s5x5_players, s5x5_procs, fuel 300,
   s5x5_run_terminates/endpoints/endpoints_size/run_recovers,
   s5x5_verifier_endpoints, s5x5_aprocs_abs, rs1/rs2, s5x5_rlayout,
   s5x5_rprocs, embed_p1/embed_p2/proj_pile + cancellations, JointSecret,
   s5x5_player_trace(+layout/p1_E/p2_E), s5x5_share_indep_p1/p2,
   s5x5_trace_secrecy, s5x5_view_secrecy_concrete, s5x5_joint_view_secrecy,
   leakage_product, s5x5_pile1/pile2_TV_bound, s5x5_spectral_TV_bound,
   var_dist_uniform_pile1/2_uniform10, s5x5_pile1_stab,
   s5x5_preserves_pile2_proved, product_scheme machinery
   (combine_secret/split_secret/pile shares/product_recon). Abelian —
   abel_sigmas, abel_s1/s2, abel_ts, abel_plug,
   abel_sum_mod_perm_compatible, abel_gens_commute, abelian_word_eval,
   freq_vec(+sum), word_eval/pgg_word, rho_from_words at (2,1),
   fdist_uniform_supp, var_dist_fdistmap_inj (relocated).
4. Final package values (types): S5 — `s5_exec_plug, s5_rand_exec_plug :
   ExecutionPlug s5_profile`; `s5_observed, s5_rand_observed :
   OE.ObservedExecution`; `s5_rand_sample : SampleAdapter R s5_rand_exec_plug`;
   `s5_word_sample : SampleAdapter R s5_exec_plug` (secretP, L
   section-parameterized). S5xS5 — the six analogues over s5x5_profile with
   product tape `('rV['Z_5]_5 * 'rV['Z_5]_5)`. Abelian — `abel_exec_plug,
   abel_shuffle_plug : ExecutionPlug abel_profile`; `abel_det_observed,
   abel_shuffle_observed : OE.ObservedExecution`; `abel_ideal_adapter :
   SampleAdapter R abel_shuffle_plug`; `abel_actual_adapter L` likewise.
   Vocabulary: `CompletionLevel, TransferStatus, PggAxiom, AssumptionStatus`
   (pgg_analysis_status.v); `AnalysisPathRow` (manifest).
5. Observers and carriers (facade aliases): S5Analysis — seat_endpoint /
   coalition_endpoints / verifier_trace / verifier_endpoints /
   player_raw_trace (raw, navigation only) / observed + the rand_ twins +
   rand_content_trace ('I_5-valued finite reader = s5_player_trace).
   S5x5Analysis — the same det/rand families on 'I_10 plus pile1_seats,
   pile2_seats, pile1_seat_view / pile2_seat_view ('Z_5), pile1/2
   coalition views ({ffun 'I_5 -> 'Z_5} per pile), joint_view (their pair).
   AbelianAnalysis — seat_endpoint, endpoint_vector (4.-tuple 'I_4,
   globally injective: endpoint_vector_inj), verifier_trace/endpoints,
   player_raw_trace, observed, shuffle_observed.
6. Sample models: S5 rand_sample (uniform iid tape `'rV['Z_5]_5`, identity
   cut), S5 word_sample (secretP x word_uniform 3 L, cut word_eval);
   S5xS5 rand_sample (Pprod = Pone x Pone, identity cut), word_sample
   (secretP x word_uniform 7 L over 8 generators); Abelian ideal_sample
   (fdist_uniform_supp on the 4-element group), word_sample
   (word_uniform 1 L.+1, cut word_eval); plus the landed PGL27/five-card
   models unchanged.
7. Theorem table (facade names): correctness — {S5,S5x5}Analysis
   exec_correct/exec_recovers/observed_recovers + rand_ triples;
   AbelianAnalysis exec_correct/exec_recovers/observed_recovers +
   shuffle_recovers (constant Ordinal 2). Security —
   S5Analysis.exec_trace_secrecy (conditional entropy),
   exec_coalition_secrecy (MI=0 + centropy, #|C| < 5);
   S5x5Analysis.exec_trace_secrecy, exec_p1_secrecy, exec_p2_secrecy,
   exec_joint_secrecy (Pprod statements against JointSecret);
   AbelianAnalysis.word_mixing_limitation (negative mixing result). Bounds —
   S5Analysis.word_endpoint_bound; S5x5Analysis.word_pile1/pile2/seat_bound
   (all conditional on s5_rayleigh_Q2_R); floors word_pile1/pile2_floor +
   word_pile1/pile2_floor_gt0 (L >= 17 regime, word_positive_regime).
   Transfer — the 10 typed status aliases + reader equalities +
   word_missing_premise + word_transfer_conditional per instance +
   Abelian chain (word_group_dist / executed_distance / sample_reader_distE
   / executed_observation_distance).
8. New bridges (endpoints): s5_sample_content_traceE (executed content
   reader at seat i = s5_player_trace i); s5_sample_coalition_viewE
   (executed coalition reader = rsh_view C); s5x5_sample_content_traceE;
   s5x5_p1_viewE / p2_viewE / p1_seat_viewE / p2_seat_viewE (executed pile
   readers = per-pile rsh_view/share through proj_pile);
   s5x5_joint_viewE (= leakage_product view); s5_word_cut_distE /
   s5x5_word_cut_distE (adapter cut distribution = rho_from_words);
   abel_shuffle_executed_readerE (executed endpoints = endpoint vector);
   abel_sample_reader_dist (executed observation distribution = reader
   pushforward of the cut distribution); the identity-cut specializations
   s5_rprocs_cut1 / s5x5_rprocs_cut1 (generalized skeleton at 1%g = landed
   randomized processes).
9. Selected Abelian negative theorem:
   `abel_executed_observation_distance : forall R L, var_dist
   (fdistmap reader (actual)) (fdistmap reader (ideal)) = 1` at the
   complete executed four-endpoint observer, actual = uniform length-L.+1
   words through word evaluation, ideal = uniform on the concrete
   four-element group. Label "fixed-length mixing limitation" is accurate:
   it states failure to mix to the named ideal at every positive length; it
   quantifies over no secret and makes no privacy claim; the proof uses the
   sign-parity class structure (not commutativity alone), and the length-0
   exclusion is witnessed by abel_word_group_dist0 = 3/2.
10. Stronger Abelian claims that remain UNPROVED (and unclaimed): any
    positive privacy theorem; any secret-dependent leakage bound for the
    secret-recovery plug; privacy failure (no reveal model is formalized);
    mixing at non-uniform word distributions.
11. Missing layers after implementation: none of the required ones. Not
    implemented (out of scope / honestly absent): S5 finite-word coalition
    claim (premise unsatisfiable), S5xS5 joint finite-word theorem,
    ideal-to-finite transfer for S5/S5xS5/five-card (missing premises named
    in the manifest appendix), pile-marginal-secret executed secrecy variant
    (probe O2 — rows name JointSecret), content-level executed transport of
    the S5xS5 sheet-endpoint floors.
12. Facade paths and section inventories:
    instances/s5/s5_analysis.v (Module S5Analysis, 38 aliases),
    instances/s5x5/s5x5_analysis.v (S5x5Analysis, 61),
    instances/abelian/abelian_analysis.v (AbelianAnalysis, 27),
    instances/pgl27/pgl27_analysis.v (43, +status alias),
    instances/kim2025/five_card_analysis.v (49, +status aliases replacing
    the empty-section-only Transfer). All use the seven fixed sections;
    S5/S5x5/five-card carry the bound sub-block.
13. Manifest rows and levels: 17 AnalysisPathRow values — pgl27 exact
    (AnalysisBridged/StaticExecutedOnly), pgl27 word
    (AnalysisBridged/IdealFinite), five-card uniform + biased
    (AnalysisBridged/StaticExecutedOnly), five-card repeated
    (Sampled/NoModelComparison), s5 det (Observed/NoModelComparison), s5
    rand (AnalysisBridged/StaticExecutedOnly), s5 word
    (Sampled/NoModelComparison), s5x5 det/rand/pile1 word/pile2 word
    (as s5, per pile), s5x5 pile1/pile2 limitation
    (Sampled/NegativeTransfer), abelian recovery + identity
    (Observed/NoModelComparison), abelian limitation
    (AnalysisBridged/NegativeTransfer).
14. Clean client evidence: exactly one Require; reaches one alias per
    section for all five facades, all nine ObservedExecution values, the
    typed vocabulary, AnalysisPathRow + all 17 rows; six Fail Checks prove
    instance internals stay qualified-only.
15. Builds: make -f Makefile.coq -j1 throughout, single rocqworker;
    baseline cone 2 min 55 s; T0 cone 6 min; per-file builds 0.9-21.3 s;
    Abelian cone 15.6 s; final client check up to date, exit 0. Warning
    categories unchanged from baseline (native-compiler-disabled,
    notation-incompatible-prefix, comment-terminator-in-string,
    abstract-large-number, deprecated-library-file); zero new warnings.
16. Audits: rocq-audit gate on all 22 commits — passed, zero bypasses; one
    H002 block fixed forward (T3.1). Stage 2 emitted the pre-existing S998
    schema no-op on every run; compensating direct rocq-auditor reviews ran
    per commit; all error-severity findings fixed forward (A002 congr1,
    H-tag retargets, retention-pin strengthening, profile_k comment); the
    T4.3 script review found nine false-pass defects, fixed with a 18-case
    regression suite.
17. Print Assumptions: Abelian path — 61 kernel-closed, 20 boolp-trio-only
    values, nothing else. S5/S5xS5 — everything touching the profiles
    reports its instance group-order axiom (via cs_plug genus-gap proofs);
    funext users add the boolp trio; s5_rayleigh_Q2_R appears exactly on
    S5Analysis.word_endpoint_bound and S5x5Analysis.word_pile1_bound,
    word_pile2_bound, word_seat_bound, word_pile1_floor, word_pile2_floor,
    word_pile1_floor_gt0, word_pile2_floor_gt0 (+ their facade aliases and
    the underlying s5x5_models lemmas). s5x5_rfree_recon and
    s5x5_combine_not_injectiveE are kernel-closed. Rows: 8 KernelClosed
    (pgl27 x2, five-card x3, abelian x3), 3 AcceptsAxioms[AxS5GroupOrder]
    (word row + AxRayleighQ2R), 6 AcceptsAxioms[AxS5x5GroupOrder] (word +
    limitation rows + AxRayleighQ2R).
18. Commits by phase: Phase 0 e262ff19 (16 probe files + ledger + response
    + plan). T0 866275a9. Phase 1 26e49487, 1ec2b94e, 50daffad. Phase 2
    2a103037, 758b2cde, 351060ba, d78fa6f2. Phase 3 08684f4a, 566613cd,
    56b388f6, 0b3b1574, 6d0a4495, ddf91838, fc8360a9. Phase 4 32b8ca82,
    149e58ff, 06ad3fea, 531a4c40, 8393e5f9, 58a049c0. Files: 3 new
    manifest-layer (status, script + test), 9 new instance files, 5 edited
    (abel_profile, s5x5_mixing, five_card_analysis, pgl27_analysis,
    pgg_collusion_bound), _CoqProject +10 lines.
19. Strongest repository-facing claim now supported: PGL27, the five-card
    family (den Boer and Kim), S5, S5xS5, and Abelian each expose one typed
    public facade with the same seven-section navigation chain from one
    probability-independent profile through actual piSMC interpreter
    executions, named executed observers, probability models, correctness,
    and their strongest justified analyses: executed exact/approximate
    privacy and transfer for PGL27; executed trace privacy, dealer
    determination and biased-cut mutual information for five-card; executed
    single-seat trace secrecy and sub-threshold coalition secrecy plus a
    conditional finite-word endpoint bound for S5; executed per-pile and
    joint secrecy, conditional per-pile endpoint bounds, and exact
    global-uniform limitation floors with a proved positive regime
    (L >= 17) for S5xS5; and a machine-checked fixed-length mixing
    limitation with exact full-L1 distance 1 at the complete executed
    endpoint observer for Abelian. Each of the 17 analysis paths states its
    typed completion, transfer, and assumption status, checked by compiled
    witnesses from a single import.
20. Nearby claims that remain FALSE and must not be made: a common template
    does not make the instances satisfy one security property; filling
    MonodromyProfile proves nothing; S5/S5xS5 finite-word rows carry no
    coalition or joint privacy (the base-distribution premise at the
    permutation carrier is absent, and for group-uniform ideals
    unsatisfiable by sign-coset confinement — not formalized at S5/S5xS5);
    endpoint mixing is not coalition privacy; the Abelian limitation is not
    a privacy failure; combine_secret recovery does not recover the
    product-secret pair (non-injectivity compiled); theorems conditional on
    s5_rayleigh_Q2_R are not kernel-closed; correctness never implies
    security.
21. Typed row matrix: item 13 plus assumption statuses in item 17 (also in
    the manifest source table with per-row justifications).
22. Theorems depending on s5_rayleigh_Q2_R (complete list, all labelled
    conditional): the landed s5_spectral_convergence_proved/gap and
    s5x5_pile1/pile2/spectral_TV_bound (pre-existing), plus the new
    s5_word_endpoint_bound, s5x5_word_pile1_bound, s5x5_word_pile2_bound,
    s5x5_word_seat_bound, s5x5_word_pile1_floor, s5x5_word_pile2_floor,
    s5x5_word_pile1_floor_gt0, s5x5_word_pile2_floor_gt0, their facade
    aliases, and the manifest rows that list AxRayleighQ2R.
23. Abelian interface migration: OLD `mp_PI = Gen_PGG_2 abel_sigmas`
    (two-generator, pi_T' = 1; the false 1 = 3 bridge); NEW
    `abel_PI := @MkPGGI abel_M 3 (ord_tuple 4) abel_starts_uniq` and
    `abel_profile := @MkMonodromyProfile abel_M 'I_4 abel_PI abel_plug`.
    Migrated consumers: none existed (verified near-orphan);
    profile_k_abel unchanged (by []); Gen_PGG_2 retains its group-level
    role in pgg_interface.v / card_exchange_pismc.v.

Request: `docs/superpowers/requests/2026-08-12-unified-instance-analysis-ROCQ-formalization-request.md`
Probes: `docs/superpowers/probes/2026-08-12-unified-instance-analysis/`
Baseline commit: `5453b93bb07b5eee63c331d17a9b95b62802b9d5` (branch `pgg-smc`).

## Phase 0 §6.1 Baseline build

Command (run from the repository root, opam switch `/Users/cheng-huiweng/Projects/coq`):

```text
make -j1 pgg-smc/manifest/pgg_analysis_client.vo \
         pgg-smc/instances/s5/s5_run.vo \
         pgg-smc/instances/s5x5/s5x5_run.vo \
         pgg-smc/instances/abelian/abel_profile.vo \
         pgg-smc/instances/abelian/abelian_word_collapse.vo
```

- Rocq: The Rocq Prover, version 9.0.0 (compiled with OCaml 5.2.1)
- OCaml: 5.2.1
- Exit status: 0
- Elapsed: 2 min 55.36 s wall (164.99 s user, 8.19 s system, 98% cpu)
- Rebuilt within the cone (stale at start, no deletions needed):
  `pgg-smc/reconstruct/rs_privacy.v`, `pgg-smc/reconstruct/rs_massey_bridge.v`,
  `pgg-smc/reconstruct/coord_perm_compatible.v`, `pgg-smc/reconstruct/cover_genus0.v`,
  `pgg-smc/instances/abelian/rigidity_abelian_instance.v`,
  `pgg-smc/instances/abelian/abel_profile.v`,
  `pgg-smc/instances/abelian/abelian_word_collapse.v`
- Warnings: all pre-existing classes only — `deprecated-library-file-since-mathcomp-2.5.0`
  (all_ssreflect), `comment-terminator-in-string` (cover_genus0.v),
  `notation-incompatible-prefix` (`_ <| _` vs `_ <| _ |> _`, abelian files). No new warnings.

## Phase 0 §6.2 Live declaration inventory

Corrected H2 description: S5 and S5xS5 are NOT "Algebraic only". Both have full
deterministic run/termination/endpoint/recovery lemma sets and randomized-tape
trace-secrecy theorems. What they lack is packaging: no `ExecutionPlug`, no
`ObservedExecution`, no `SampleAdapter`, no facade. Abelian additionally has an
incoherent profile interface (below).

### Reference shape (landed at `88ed16a2`)

- `MonodromyProfile` (protocol/pgg_monodromy_profile.v:52): mp_M, mp_secretT,
  mp_PI, mp_plug. `ExecutionPlug mp` (protocol/pgg_execution_plug.v:56):
  ep_inputT, `ep_players_bridge : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp))`,
  ep_players, ep_playersE, ep_content, ep_input_procs, ep_fuel; smart
  constructors `dealer_secret_plug` / `committed_input_plug`.
  `OE.ObservedExecution` (protocol/pgg_observed_execution.v:89): oe_profile,
  oe_execution, oe_P_idx, oe_content_obs, oe_expected, oe_terminates,
  oe_endpoints, oe_static_recon. `SampleAdapter R mp e`
  (security/pgg_sample_adapter.v:114): sa_sampleT, sa_sampleP, sa_arg, sa_cut.
- `PGGInterface M` (protocol/pgg_interface.v:379): pi_T', pi_starts
  (`pi_T'.+1`-tuple, uniq). Seats = `pi_T'.+1`.
- Facades: `Module PGL27Analysis` / `Module FiveCardAnalysis`, seven
  `===== k. <Section> =====` markers, aliases only; five-card section 7 is
  documented-empty. Manifest = prose row tables (10 fixed fields + capability
  table + level justification) + `Timeout 60 Check (alias : spelled_type)`
  checker; client = exactly one `Require Import pgg_analysis_manifest` +
  bare `Check` per section + `Fail Check` encapsulation probes.
- Confirmed absent repo-wide: `CompletionLevel`/`TransferStatus`/
  `AssumptionStatus` as Rocq identifiers; `NoModelComparison`,
  `StaticExecutedOnly`, `IdealFinite`, `NegativeTransfer` occur only in the
  request. Phase 4 must introduce the typed vocabulary.
- Generic transfer theorem exists: `var_dist_fdistmap_transfer`
  (security/pgg_collusion_bound.v:1185), premises `var_dist P Q <= delta` and
  `fdistmap fx Q = fdistmap fy Q`, conclusion bound `delta + delta`.
- `var_dist` (probability/variation_dist.v:33) is full (un-halved) L1.

### S5 (files s5_profile.v, s5_run.v, s5_trace.v, s5_secrecy.v, s5_mixing.v, rigidity_s5_instance.v)

- Profile: `s5_profile := @MkMonodromyProfile s5_M 'I_5 s5_PI s5_plug`;
  `s5_PI = @MkPGGI _ 4 (ord_tuple 5)` (5 seats); scheme `sum_mod_scheme 3 4`
  (ts_T' = ts_k' = 4); `profile_k_s5 = 5`.
- Deterministic path (s5_run.v, no sections, R-free): `s5_players` = 5 explicit
  ordinals (s5_run.v:50), `s5_procs s w0` (dealer with
  `ts_encode s5_scheme s`, cut-parametric), fuel 150,
  `s5_run_terminates` (`= nseq 7 Finish` shape), `s5_endpoints`,
  `s5_endpoints_size`, `s5_run_recovers` (premise `w0 \in pgg_G s5_M`).
- Randomized path (s5_trace.v, Section with `Variable R`): abstract skeleton
  `s5_aprocs_abs (g : 'I_5 -> 'I_5)` with cut HARD-WIRED to `1%g`;
  `s5_rs := @unif_randomized_sharing R 3 4` over tape `'rV['Z_5]_5`
  (coord 0 = secret `'Z_5`, coords 1-4 masks; share 4 = secret - sum masks);
  `s5_rlayout u = [tuple rsh_share s5_rs i u | i < 5]`;
  `s5_rprocs u = s5_aprocs_abs (tnth (s5_rlayout u))`; distribution
  `s5P := fdist_uniform (card_ZN_subproof 3) `^ 5` (a Let — must respell);
  `s5_player_trace i` reads `content_of` at proc index `2+i`;
  `s5_player_trace_E : s5_player_trace i = rsh_share s5_rs i`;
  `s5_trace_secrecy : `H(rsh_secret s5_rs | s5_player_trace i) = `H `p_ ...`
  (conditional entropy ONLY; via `trace_secrecy_of_view`).
  Name collision: `s5_trace.s5_players` duplicates `s5_run.s5_players`.
- Static secrecy: `s5_view_secrecy_concrete (C : {set 'I_5}) (#|C| < 5)`
  gives MI = 0 AND conditional entropy preserved, coalition view carrier
  `{ffun 'I_5 -> 'Z_5}` via `rsh_view`, same tape distribution as `s5P`.
- Mixing (s5_mixing.v, no sections): `s5_alpha_R = 181/200`; the single
  Axiom `s5_rayleigh_Q2_R`; `s5_spectral_convergence_proved/gap (R L s)` bound
  `var_dist (fdistmap (fun sigma => sigma s) (rho_from_words L (path_gen_tuple 3)))
  (uniform 5) <= sqrt 5 * alpha^L` — a SINGLE-POSITION endpoint pushforward of
  the word distribution, not a cut/coalition distance.
- Consumers outside s5/: only s5x5_mixing.v (s5_rayleigh_Q2_R, s5_alpha_R*);
  everything else zero — packaging is additive.

### S5xS5 (s5x5_profile.v, s5x5_run.v, s5x5_trace.v, s5x5_secrecy.v, s5x5_mixing.v, rigidity_s5x5_instance.v, pgg_s5x5.v, s5x5_pile.v)

- Profile: `s5x5_profile` on `@Gen_PGGTypes 7 8 s5x5_gen_tuple` (10 sheets,
  8 adjacent-transposition generators, 4 per pile), secret `'I_10`, scheme
  `product_scheme (sum_mod_scheme 3 4) (sum_mod_scheme 3 4)`
  (ts_T' = 9, ts_k = 5); `profile_k_s5x5 = 5`.
- `combine_secret s1 s2 = (s1 + 5*s2) %% 10`; `split_combineK` PARTIAL
  (hypothesis `s1 + 5*s2 < 10`, i.e. holds only for `s2 < 2`);
  `combine_splitK` total. Randomized recovery must therefore work from the two
  factor sum reconstructions + pile preservation, as the request instructs.
- Deterministic path: `s5x5_players` = 10 explicit ordinals, `s5x5_procs s w0`,
  fuel 300, 12 procs, `s5x5_run_terminates` (`nseq 12 Finish`),
  `s5x5_endpoints`, `s5x5_endpoints_size` (= 10), `s5x5_run_recovers`
  (premise `w0 \in pgg_G`).
- Randomized path: `rs1 = rs2 = @unif_randomized_sharing R 3 4`; product tape
  `uv : 'rV['Z_5]_5 * 'rV['Z_5]_5`, `Pprod := Pone `x Pone` (Pone is a Let);
  codec `embed_p1 = inord (val s)`, `embed_p2 = inord (5 + val s)`,
  `proj_pile c = inord (val c %% 5)` with `cancel_p1/p2`;
  `s5x5_rlayout`, `s5x5_rprocs uv` (identity cut, abstract skeleton);
  `JointSecret uv = (rsh_secret rs1 uv.1, rsh_secret rs2 uv.2) : 'Z_5 * 'Z_5`;
  `s5x5_player_trace j` at proc `2+j`;
  `s5x5_trace_secrecy (j : 'I_10) : `H(JointSecret | s5x5_player_trace j) = `H `p_ JointSecret`.
- Static: `s5x5_view_secrecy_concrete (C1 C2 : {set 'I_5}, #|Ci| < 5)` per-pile
  MI = 0 + centropy; `s5x5_joint_view_secrecy` via `leakage_product` over
  `P `x P` — same product distribution shape as `Pprod`.
- Mixing: `s5_lazy_alpha_R = (1 + s5_alpha_R)/2`; `s5x5_pile1_TV_bound` /
  `s5x5_pile2_TV_bound` (endpoint pushforward vs `fdist_uniform_pile{1,2}`,
  bound `sqrt 5 * lazy_alpha^L`); `s5x5_spectral_TV_bound` (vs uniform 10,
  bound `1 + sqrt 5 * lazy_alpha^L`); PROVED exact floors
  `var_dist_uniform_pile1_uniform10 = 1` (s5x5_mixing.v:871) and pile2 (:901)
  — the NegativeTransfer rows' first factor already exists. All spectral
  results depend on `s5_rayleigh_Q2_R`.
- Pile structure: indices 0-4 / 5-9 of `'I_10`; `widen5to10` / `rshift5to10`;
  `s5x5_pile1_stab` (axiom-free pile preservation);
  `product_sum_mod_perm_compatible` needs only pile-1 preservation.
- Axiom surface beyond Rayleigh (rigidity path only): `s5x5_group_order_eq`,
  `s5x5_inverse_galois_realised`, `s5x5_multi_realised`. The run path is
  deliberately routed around them. Zero consumers outside the directory.

### Abelian (abel_profile.v, abelian_word_collapse.v, rigidity_abelian_instance.v, pgg_abelian.v)

- Generators: `abel_s1 = tperm 0 1`, `abel_s2 = tperm 2 3` in `'S_4` (two
  disjoint transpositions; generated group Klein Z/2 x Z/2, order 4 — order
  fact NOT yet a repo lemma). `abel_ts := @sum_mod_scheme 2 3`
  (ts_T' = 3, 4 shares over 'I_4), `abel_plug` with `rp_content = id`.
- Incoherence CONFIRMED: `mp_PI abel_profile = Gen_PGG_2 abel_sigmas` has
  `pi_T' = 1` (2 seats) while `ts_T' abel_ts = 3`; `ExecutionPlug` requires
  `ep_players_bridge : pi_T' = ts_T'`, i.e. the false `1 = 3`.
- Migration surface is near-orphan: `Gen_PGG_2 abel_sigmas` is used as a
  profile interface ONLY at abel_profile.v:73; `abel_profile` and
  `profile_k_abel` have zero consumers. Four-seat replacement
  `abel_PI := @MkPGGI (Gen_PGGTypes abel_sigmas) 3 (ord_tuple 4) uniq` follows
  the s5/pgl27 pattern verbatim; `abel_HT := erefl`, `abel_G_stable` one-liner.
- Word collapse: `abelian_word_eval` (word_eval = prod of gen^freq),
  `freq_vec_det`, `freq_vec_sum`, `abelian_search_space_bound`
  (<= 'C(L+1,1) = L+1 at Tg = 2 — too weak for the negative target).
- Reachability at fixed length (NOT yet a lemma anywhere): for L >= 1,
  `achievable L` = one parity class of exactly 2 elements
  ({s1, s2} for odd L; {1, s1*s2} for even L >= 2) out of |G| = 4; the uniform
  word distribution pushes to the UNIFORM distribution on that class
  (P(c1 odd) = 1/2). Hence var_dist(actual, uniform-on-G) =
  2*(1/2 - 1/4) + 2*(1/4) = 1 exactly, at every positive length. The complete
  endpoint vector with identity content is globally injective on `{perm 'I_4}`,
  so the distance transports to the executed observer
  (`var_dist_fdistmap_inj` pattern, s5x5_mixing.v:329).
- `weval_inj` is FALSE for L >= 2 (2^L words, 2 achievable elements), so the
  probe must use `security_witness_from_bound`-style statements, never the
  `Hlfree`-carrying constructors. `rho_from_words` itself needs no Hlfree:
  `@rho_from_words R 2 1 L abel_sigmas : R.-fdist {perm 'I_4}`.
- `abel_security_witness_direct_1` (L = 1, eps = 1) via endpoint injectivity;
  consumed by `abel_rigidity` only.

## §18 fresh independent re-audit

### Naming/API/architecture audit: VERDICT GO

Findings adopted into the plan:

1. Module names: `Module S5Analysis` in `s5_analysis.v`, `Module S5x5Analysis`
   in `s5x5_analysis.v` (identifier family is uniformly `s5x5`),
   `Module AbelianAnalysis` in `abelian_analysis.v`. No collisions repo-wide.
2. Dual-plug alias names (request leaves them open): deterministic path keeps
   pgl27-parity names (`exec_plug`, `observed`, `exec_correct`,
   `exec_recovers`); randomized path gets `rand_` prefix (`rand_exec_plug`,
   `rand_observed`, `rand_correct`, `rand_recovers`). S5x5 observer aliases
   carry pile tags (`pile1_seat_endpoint`, `pile2_coalition_view`,
   `joint_view`).
3. Cross-file duplicates (complete): only `s5_players` (s5_run.v:50 vs
   s5_trace.v:44, identical bodies) forces qualification; `content_of` has
   four copies (s5_trace, s5x5_trace, pgl27_trace, denboer_trace) — import
   discipline: no file Imports two `*_trace` modules; `content_of` written
   qualified in any file importing more than its own instance cone.
   §8.1's implied `s5x5_players` collision does not exist (defined once).
4. Typed vocabulary placement: new `pgg-smc/manifest/pgg_analysis_status.v`
   (no pgg imports; `Inductive CompletionLevel/TransferStatus/AssumptionStatus`),
   `_CoqProject` insertion after `pgg_observed_execution.v` (line 141);
   facades `Require Export` it; manifest/client inherit through facades
   (placing it inside the manifest would be an import cycle). All constructor
   names collision-free as identifiers. `AssumptionStatus` needs a
   data-carrying constructor: `KernelClosed | AcceptsAxioms of seq string`
   (or a dedicated axiom-label enum).
5. New files (precedent pgl27_exec/models/analysis): `s5_exec.v`, `s5_models.v`,
   `s5_analysis.v` (after `s5_trace.v`, line 233); `s5x5_exec.v`,
   `s5x5_models.v`, `s5x5_analysis.v` (after line 240); `abel_profile.v`
   edited in place; `abelian_exec.v`, `abelian_models.v`,
   `abelian_analysis.v` (after line 245); manifest Require Export line
   extended with the three new facades.
6. Tag grammar: request §11 matches AUTHORITY.md and configured
   `main_purpose_labels` exactly. Typed status names are I001-exempt
   (CamelCase). Watch: 5-component lowercase lemma names for the
   NegativeTransfer floors need a canonical tail or `Naming:` line.
7. Completeness check: `pgg-smc/scripts/profile_facade_check.sh` modeled on
   `abstract_metrics.sh` (tracked-files universe via git ls-files, comment
   stripping, pinned expected list, `Let`-aware, `*_analysis.v` facade aliases
   excluded, den_boer alias kept). Verified universe: exactly
   {s5, pgl27, five_card, abel, s5x5}_profile + den_boer alias; nothing in
   oc/monster/cyclic/star.
8. Every load-bearing identifier in the request exists at the cited location.
9. Transfer statuses are per PATH: five-card rows 3-4 `StaticExecutedOnly`,
   row 5 (repeated/centi endpoint bounds) `NoModelComparison`. Do not stamp a
   whole facade.
10. The unnumbered `===== bound (endpoint marginal, not security) =====`
    sub-block is part of the facade template for S5/S5x5 conditional endpoint
    bounds. Prose level `Security-bridged` migrates to typed `AnalysisBridged`
    in Phase 4 (a manifest label, not a mathematical rename).

### Soundness audit: VERDICT GO

All six audited claim groups verified by hand against sources; four MINOR
corrections folded in:

1. Abelian §6.7 target VERIFIED: group = Klein four-group; support at length
   n >= 1 is one sign-parity class of 2 elements, pushforward uniform on it;
   full-L1 distance to group-uniform exactly 1 for every n >= 1 (length 0,
   distance 3/2, correctly excluded). The proof needs the parity structure,
   not commutativity alone (adding an identity generator keeps abelianness
   but destroys distance 1) — §9.6's warning is necessary and satisfiable.
   Identity-content recovery constant: recon = (0+1+2+3) mod 4 = 2, i.e.
   `Ordinal 2 : 'I_4`, constant across all of S_4.
2. MINOR (folded): state endpoint-vector injectivity GLOBALLY on
   `{perm 'I_4}` (holds; a permutation is determined by all 4 images);
   `var_dist_fdistmap_inj` requires global injectivity and then gives exact
   equality, which "exact distance 1" needs.
3. MINOR (folded): `var_dist_fdistmap_inj` currently lives in
   `s5x5_mixing.v` inside an R-section; relocate/re-prove in a shared file
   (`pgg_collusion_bound.v`, next to var_dist_triangle) so abelian does not
   import s5x5_mixing.
4. MINOR (folded): §9.8's "second capability" labelling sentence is
   off-by-one — the fixed-length mixing-limitation label belongs to row 3
   (the limitation theorem), row 2 is correctness.
5. S5xS5 NegativeTransfer rows VERIFIED: var_dist_triangle
   (pgg_collusion_bound.v:44) + symmetric_var_dist give
   `>= 1 - sqrt 5 * lazy_alpha^L`; positive regime exactly **L >= 17**
   (sqrt 5 * 0.9525^16 ~ 1.026 > 1 > 0.978 ~ at 17); in-kernel needs a
   rational sqrt-5 bound (same shape as landed 2^-40 proofs). Floors are
   axiom-free; upper bounds conditional on s5_rayleigh_Q2_R.
6. S5 randomized recovery VERIFIED: sum-mod recon telescopes
   (masks + (secret - sum masks)); codec 'Z_5 -> 'I_5 essentially identity;
   `s5_sum_mod_perm_compatible` is Qed axiom-free and covers every cut in
   pgg_G.
7. MINOR (folded): `s5_plug`/`s5x5_plug` are projections of covering records
   whose proofs use `s5_group_order_eq`/`s5x5_group_order_eq`; every value
   routed through the profiles reports the group-order axiom under
   Print Assumptions even on correctness paths. S5/S5xS5 manifest rows will
   carry AcceptsAxioms(...) status, disclosed per §12.18/§12.20; a
   re-bundled standalone plug is excluded by §5.1/§12.2.
8. S5 §7.7 discipline VERIFIED AND SHARPENED: the missing transfer premise
   is `var_dist (rho_from_words L (path_gen_tuple 3)) Q <= delta` on carrier
   `{perm 'I_5}` against a named ideal Q — and for Q = uniform on the group
   it is UNSATISFIABLE for small delta: every length-L word of transpositions
   lies in one sign coset, so var_dist >= 1 for every L. NoModelComparison is
   mathematically forced for this path (same parity mechanism as the Abelian
   target). Record under "nearby claims that remain false".
9. Five-card StaticExecutedOnly alias: pure packaging, no new mathematics.
10. S5xS5 §8.1 warnings are necessary, not cautious: product_valid at the
    combine image genuinely fails for s2 in {2,3,4}; factor-sum recovery
    works because all 8 generators are within-pile transpositions.

## Phase 0 §6.3–6.8 Probes

Probe directory: `docs/superpowers/probes/2026-08-12-unified-instance-analysis/`
(build via its `rebuild.sh`, one worker; ledger in `probe-ledger.md`).
Probe files CAN Require each other through the `uia_probe` logical root once
the sibling `.vo` exists (demonstrated by `probe_require_check.v`).

### S5 probes (§6.3–6.6): GO

Files (all exit 0, zero Admitted/Abort/Axiom, mutation-checked):
`probe_s5_det_plug.v` (4.8 s, assumptions: s5_group_order_eq only),
`probe_s5_rand_plug.v` (5.1 s, + boolp trio on the two R-bridging lemmas),
`probe_s5_adapters.v` (6.3 s, + s5_rayleigh_Q2_R on s5_word_endpoint_bound
only), `probe_s5_mutation.v` (5.0 s), `probe_require_check.v` (3.2 s).

Working constructor terms (verbatim in the probes):
- `s5_det_plug := @dealer_secret_plug mpS 'I_5 erefl s5_run.s5_players
  s5_players_enumE (fun s _ => tnth (ts_encode s5_scheme s)) 150`
- `s5_rand_plug := @dealer_secret_plug mpS 'rV['Z_5]_5 erefl
  s5_run.s5_players s5_players_enumE (fun u _ => tnth (s5_rfree_layout u)) 150`
- Both `OE.MkObservedExecution` values; `s5_rand_observed`'s expected value is
  `fun u => s5_codec (s5_tape_secret u)` with codec = identity
  ('Z_5 and 'I_5 definitionally equal; cancellations by []).
- `s5_rand_sample` (sampleT 'rV['Z_5]_5, prior = respelled s5P, arg idfun,
  cut = fun _ => 1%g); `s5_word_sample` (prior secretP x word_uniform 3 L,
  cut = word_eval).
- Convertibility by []: `exec_procs mpS s5_det_plug s w0 0 = s5_procs s w0`;
  `exec_procs mpS s5_rand_plug u w0 0 = s5_rprocs_cut u w0`;
  `s5_aprocs_cut g 1%g = s5_aprocs_abs g`.

§6.6 answers: (a) YES — respelled s5P accepted verbatim;
`s5_sample_content_traceE` + `s5_sample_trace_secrecy` restate
s5_trace_secrecy at the executed reader. (b) YES — coalition carriers agree
(`{ffun 'I_5 -> 'Z_5}` = `{ffun 'I_5 -> 'I_5}`), seat indexing via
s5_rho1_index, `s5_sample_coalition_viewE`; s5_view_secrecy_concrete reaches
the executed reader for every #|C| < 5. (c) YES —
`s5_word_cut_distE : sa_cut_dist s5_word_sample = rho_from_words L
(path_gen_tuple 3)`; spectral bound discharges at the adapter's own cut
distribution. (d) NO for the coalition reader — missing premise named as
`var_dist (sa_cut_dist s5_word_sample) Q <= delta` at carrier `{perm 'I_5}`;
mutation 8 proves the endpoint bound does not cast into it;
`NoModelComparison` stands.

Discharged obligations to carry into Phase 1: `s5_rfree_shareE` (funext +
sumrRVE; the only boolp-trio source), `zp5_sum_val` (nat/'Z_5 sum bridge),
`s5_rfree_sum` (shares telescope to the tape secret), and
`s5_recon_perm_invariant` (the inline `have` of s5_run_recovers, named).
Packaging fact: everything mentioning s5_profile inherits s5_group_order_eq
through cs_plug (run never exercises it) — assumption status per audit
finding 7.

### S5xS5 probes (§6.3–6.6): GO

Files (all exit 0, zero Admitted/Abort/Axiom): `probe_s5x5_det_plug.v`
(5.5 s, s5x5_group_order_eq only), `probe_s5x5_rand_plug.v` (5.9 s;
s5x5_rfree_recon CLOSED under global context; layout/cut lemmas boolp trio),
`probe_s5x5_adapters.v` (16.9 s; spectral results add s5_rayleigh_Q2_R),
`probe_s5x5_mutation.v` (45.6 s; 15 perturbations rejected).

Working constructors: det plug `@dealer_secret_plug mpX 'I_10 erefl
s5x5_players s5x5_players_enumE (fun s _ => tnth (ts_encode s5x5_scheme s))
300`; rand plug over `('rV['Z_5]_5 * 'rV['Z_5]_5)` with R-free layout;
`erefl` bridge works (pi_T' = ts_T' = 9); `exec_procs ... = s5x5_procs s w0`
by []; rand adapter with respelled Pprod definitionally equal (by []) to the
trace file's; word adapter with `sa_cut_dist = @rho_from_words R 8 7 L
s5x5_gen_tuple` exactly.

Randomized recovery route (no ts_valid, axiom-free `s5x5_rfree_recon`):
(1) `s5x5_reconE` by [] unfolds product recon to combine_secret of pile
recons; (2) pile-share extraction rewritten to probe seat embeddings
(val_inj on boundedness proofs); (3) cut-permuted layout reindexed by
`s5x5_p1_map/p2_map` using s5x5_pile1_stab + s5x5_preserves_pile2_proved and
codec cancellations; (4) `sum_mod5_recon_reindex` (reindex-by-injection
version of the S5 invariance proof) at the per-pile validity from the S5
probe's s5_rfree_valid.

§6.6 answers: (a) YES (Pprod definitional); (b) carrier/indexing YES via
proj_pile codec, but s5x5_view_secrecy_concrete lives over the SINGLE-pile
distribution — executed per-pile rows are new Pprod statements against
JointSecret (obligation O1), compiled as s5x5_p1_secrecy/p2_secrecy;
joint reader matches leakage_product view and s5x5_joint_view_secrecy
restates directly. (c) YES exactly. (d) NO — missing premise
`var_dist (sa_cut_dist s5x5_word_sample) Q <= delta` at `{perm 'I_10}`;
Fail-guard confirms the pile bounds do not cast into it.

NegativeTransfer floors COMPILED: `s5x5_word_pile1_floor`/`pile2_floor`:
`1 - sqrt 5 * lazy^L <= var_dist (endpoint pushforward) (uniform 10)` via
var_dist_triangle + exact pile floors + conditional pile bounds. L >= 17
positivity corollary deferred to Phase 2 (statement recorded in comment).

Carry-forward obligations: O1 (per-pile secrecy = Pprod statement, not a
restatement), O2 (pile-marginal-secret variant unprobed; manifest must name
which secret each row is about), O3 (recovery field is the 'I_10 image only;
combine_secret non-injectivity compiled), O4 (missing base premise), O5
(positivity regime), O6 (s5x5_group_order_eq on every profile-touching
value; only s5x5_rfree_recon is closed), O7 (mutation messages are expected
shapes, not harvested transcripts — compiled rejections certify).

### Abelian probes (§6.3, §6.7): GO

Files (all exit 0, zero Admitted/Abort/Axiom): `probe_abel_profile.v` (5.0 s,
all Closed under the global context), `probe_abel_plugs.v` (5.2 s, all
Closed), `probe_abel_negative.v` (5.7 s, R-carrying results boolp trio only),
`probe_abel_sig.v` (4.6 s), `probe_abel_mutation.v` (4.9 s). `abel_plug` is
axiom-FREE — nothing on the Abelian path touches s5_rayleigh_Q2_R or any
covering record.

Old bridge confirmed false (`Fail` with the pi_T'/ts_T' mismatch harvested);
new interface compiles: `abel_PI := @MkPGGI abel_M 3 (ord_tuple 4)
abel_starts_uniq`, `abel_profileP := @MkMonodromyProfile abel_M 'I_4 abel_PI
abel_plug`, bridge `erefl` (3 = 3), `profile_k abel_profileP = 4` by [].
Klein facts in-kernel: `abel_G4 = [set 1; s1; s2; s1*s2]` equals
`pgg_G abel_M`, cardinality 4, abelian.

Both plugs at fuel 150 (6 procs; vm_compute < 0.5 s with abstract leaves,
S5-pattern generic verifier-endpoints lemma): secret-recovery plug
(`ts_encode abel_ts`, recovery for every s and every cut in pgg_G) and
identity-content shuffle plug (ep_inputT = unit, content idfun; constant
recovery `abel_identity_recon_value = Ordinal 2` — holds for EVERY
permutation cut, not only group cuts). Both OE values compile. Complete
endpoint-vector reader `abel_reader sigma = [tuple sigma (start i) | i]`
GLOBALLY injective.

Negative target: compiled EXACTLY as pinned, and stronger — no parity side
condition:

```coq
abel_word_group_dist : forall (R : realType) (L : nat),
  var_dist (abel_word_dist R L) (abel_group_uniform R) = 1%R
abel_executed_distance : forall (R : realType) (L : nat),
  var_dist (fdistmap abel_reader (abel_word_dist R L))
           (fdistmap abel_reader (abel_group_uniform R)) = 1%R
abel_adapter_distance / abel_executed_observation_distance : (at the two
  SampleAdapters' own sample spaces, = 1%R)
abel_word_group_dist0 : length-0 distance = 1 + 2^-1  (exclusion witness)
```

with `abel_word_dist R L := @rho_from_words R 2 1 L.+1 abel_sigmas` and
`abel_group_uniform := fdist_uniform_supp abel_G4`. The counting lemma was
replaced by a bijection argument: flip-letter-0 involution + reindex_inj +
bigID against FDist.f1 gives class mass 1/2 directly. Label confirmed:
fixed-length mixing limitation (not privacy failure). Both parity classes
handled ({s1,s2} odd; {1,s1s2} even), distance 1 in both.

Carry-overs for Phase 3: rename abel_profileP -> abel_profile + migrate
(near-orphan); var_dist_fdistmap_inj relocation (= plan D6); SampleAdapter is
a primitive-projection record — `sa_cut u` never `sa_cut sa u`, while
sa_sampleT/sa_sampleP take the record explicitly (cost two compiles here,
will bite in Phases 1-2).

### Facade/manifest graph probe (§6.8): GREEN

`probe_facade_graph.v` (exit 0, 4.5 s): typed vocabulary
(CompletionLevel/TransferStatus/PggAxiom/AssumptionStatus) elaborates with no
collisions against the full S5 import closure; `AnalysisPathRow` with the
dependent `forall R, option (SampleAdapter ...)` slot instantiated at both an
Observed-level row (no model) and an AnalysisBridged-level row
(`Some (s5_rand_sample R)`); facade-skeleton module exposes typed
transfer-status aliases reachable by qualified bare Check (the clean-client
pattern); mutation guards hold. Import graph (status -> facades -> manifest ->
client) acyclic by construction; the exact `_CoqProject` insertion plan is in
the probe file header.

## Phase 0 §6.9 Verdicts

| Instance | Verdict | Evidence |
|---|---|---|
| S5 | **GO** | probe_s5_det_plug / rand_plug / adapters / mutation green; both plugs + OEs + adapters compile; executed secrecy bridges via reader equalities; missing transfer premise named |
| S5xS5 | **GO** | probe_s5x5_* green; randomized combine_secret recovery proved WITHOUT ts_valid (axiom-free); pile/joint readers typed; NegativeTransfer floors compiled |
| Abelian | **GO** | probe_abel_* green; four-seat interface + revised profile compile; §6.7 distance = 1 machine-checked at every positive length; axiom-free beyond boolp |

Both §18 re-audits: GO (findings folded above). Phase 0 is complete; the
implementation plan is at
`docs/superpowers/plans/2026-08-12-unified-instance-analysis-implementation-plan.md`.

## Phase 0 §6.9 Verdicts

(pending)
