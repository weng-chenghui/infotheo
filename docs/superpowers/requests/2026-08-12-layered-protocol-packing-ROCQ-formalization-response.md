# Implementation response: layered protocol packing and field migration

Date: 2026-08-12. STATUS: COMPLETE (stages A-H1 implemented; H2 delivered as
inventory + order, per the request's own scoping).

Request: `docs/superpowers/requests/2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`
(amended with the §16.4 fold-back record).
Plan: `docs/superpowers/plans/2026-08-12-layered-protocol-packing-implementation-plan.md`
(the as-built deviations are recorded in section 9 below).
Probes: `docs/superpowers/probes/2026-08-12-layered-protocol-packing/`
(17 files + probe-ledger.md + migration-inventory.md + migration-matrix.md +
baseline-shinagawa21-before.md), committed at `acbd8482`.
Implementation commits: `9fdec47f` (T1), `14930f5f` (T2, stages A-C),
`d66219a3` (T3-T5, stages D-G), `b4a163d0` (T6-T7, stage H1).
41 files changed, 3869 insertions, 593 deletions, from base `995e2a39`.
Every commit passed the rocq-audit pre-commit gate without bypass.

## 1. Stage verdicts (§20 item 1)

| Stage | Verdict | Evidence |
|---|---|---|
| Probe gate §15 (units A-F) | GO — all seven green | probe-ledger.md; zero Admitted/Abort/Axiom; boolp-trio-or-closed; all mutations red |
| §16.1 soundness re-audit | VERDICT: GO | 21 findings, 4 MAJOR (Section 13 new scope), folded as §16.4 |
| §16.2 API/naming re-audit | VERDICT: GO | 24 findings + per-file migration table, folded as §16.4 |
| Stage A (mp_security removal, R-free program layer) | DONE | `14930f5f`; all five profiles are closed terms |
| Stage B (optional slots to bundle; ep_cards_bridge removal) | DONE | `14930f5f`; every attachment preserved |
| Stage C (retained-field comments) | DONE | `14930f5f` (§14.2 sweep incl. §16.4 item 9) |
| Stage D (ObservedExecution) | DONE | `d66219a3`; both values Closed under the global context |
| Stage E (sample models) | DONE | `d66219a3`; all six required models at the pinned carriers |
| Stage F (analysis bridges) | DONE | `d66219a3`; executed 2^-39 bridges, Kim MI transport, den Boer ties |
| Stage G (generic transfer) | DONE | `9fdec47f` + PGL instantiation in `d66219a3` |
| Stage H1 (facades + manifest) | DONE | `b4a163d0`; 89 aliases, 5-row manifest, one-import client |
| Phase H2 | inventory + order delivered (section 12); no facades implemented, per request §13.4 |

## 2. Shinagawa 2021 distance (the meta-goal)

Baseline: Shinagawa, "Card-based Cryptography with Dihedral Symmetry",
New Generation Computing 39, 2021. Metric and BEFORE evidence:
`baseline-shinagawa21-before.md`. BEFORE: **5/16**. AFTER (frozen
procedures re-run at `b4a163d0`, `baseline-shinagawa21-after.md`):
**8/16, delta +3** — V5 (protocol/security separation) 0 to 1, V8
(per-instance entry point) 0 to 2, the two virtues stages A and H1
targeted; V2 stays partial pending the H2 rows (s5/s5x5); V6 (scope
statement + retired-instance build cleanup) and V5's directory-hygiene
half remain, both outside this request's scope with a mapped route.

## 3. Final record shapes (§20 item 2)

- `MonodromyProfile` (protocol/pgg_monodromy_profile.v): mp_M, mp_secretT,
  mp_PI, mp_plug — no realType, no security field.
- `ExecutionPlug (mp : MonodromyProfile)` (protocol/pgg_execution_plug.v):
  ep_inputT, ep_players_bridge, ep_players, ep_playersE, ep_content,
  ep_input_procs, ep_fuel — no realType, no cards bridge; generic API
  exec_* R-free; new exec_verifier_trace + exec_endpoints_verifier_traceE.
- `ShuffleMarginalBound (R) (M)` (reconstruct/algebraic_rigidity.v):
  sw_L, sw_bound_eps, sw_rho_dist, sw_bound (+ the four Arguments lines).
- `ShuffleCertificateBundle (R) (M)`: scb_bound, scb_exact, scb_asymptotic;
  shuffle_bundle_of_bound maps a bound to a bundle with both slots None.
- `AlgebraicRigidity.ar_security` / `CombinatorialRigidity.cr_security`:
  bundles; `SecurityProfile.sp_witness` / `CertifiedSolution.cs_witness`:
  bounds; `certified_from_bound` replaces certified_from_witness.
- `SampleAdapter (R) (mp) (e)`: unchanged four fields; R now explicit at
  type ascriptions (mp no longer determines it) — as-built API note.
- `OE.ObservedExecution` (protocol/pgg_observed_execution.v): the §9
  skeleton verbatim, in a module under Unset Implicit Arguments; five
  one-line derivations through the generic theorems; five extractor
  specializations; no generic semantic raw-row equation.

## 4. Removed fields and replacement paths (§20 item 3)

| Removed | Replacement |
|---|---|
| MonodromyProfile.mp_security + record R | named values: pgl27_marginal_bound + pgl27_certificate_bundle, fc_kim_security_bundle (+ kim_security_bundle_centi), den_boer_marginal_bound, s5/s5x5/oc/monster/abelian/cyclic bounds + Schreier bundles |
| SecurityWitness (ctor arity 6) | ShuffleMarginalBound + ShuffleCertificateBundle, atomic, no alias, no shipped converter |
| sw_exact / sw_asymptotic slots | scb_exact / scb_asymptotic; all eight Some-carrying producers preserved (probe B projection equations) |
| ExecutionPlug.ep_cards_bridge + record R | removed with its only consumer; seat/share coherence via ep_players_bridge unchanged |
| exec_content_from_plug | deleted (zero consumers) |
| profile_eps / profile_anonymous | sw_bound_eps / sw_bound of named bounds; profile_eps_pgl27 restated (= 0, same name) |
| five_card_witness_cut_dist | deleted (zero external refs); Kim bound preserved in the bundle |
| pgl27_witness_cut_dist | inlined into pgl27_sample_cut_distE |
| kim_profile wrapper | deleted (orphaned); den_boer_profile := five_card_profile remains |

## 5. Retained non-obvious fields (§20 item 4)

All §14.2 comments landed in `14930f5f`/`d66219a3`: ep_players
(computational cache; measured 0.016-0.022 s vs stuck enum), ep_playersE
(canonical enumeration), ep_players_bridge (seat/share type coherence),
ep_fuel (interpreter budget), sw_L (word length; consumer list in module
overview), sw_rho_dist/sw_bound_eps/sw_bound (per-position marginal only),
scb_* (optional attachments that never change the core bound; the sw prefix
documented as historical), mp_M/mp_secretT/mp_PI/mp_plug, ep_inputT/
ep_content/ep_input_procs (run argument vs deck vs input mode), the four
SampleAdapter fields, sa_joint_dist (finite argument reader), the five
raw-trace extractors + verifier twin with observer-scope comments, and all
eight ObservedExecution fields (dependency order; group membership only on
oe_static_recon).

## 6. Package values and bridges (§20 items 5-6)

Values: `pgl27_observed`, `five_card_observed` (shared by den Boer and Kim;
`den_boer_observed` core-equal by `by []`), both parameterless and Closed
under the global context. Sample models: pgl27_sample, pgl27_word_sample,
pgl27_fixed_sample s, pgl27_fixed_word_sample s; five_card_sample,
kim_single_sample, kim_repeated_sample, kim_centi_repeated_sample — the
§10.1/§10.2 carriers verbatim.

Bridges to existing security results (each an exact equality or rewrite
chain, never a name match):
- PGL exact: pgl27_exact_coalition_distE + pgl27_exec_exact_view_indep
  (executed coalition distribution in the independence product identity).
- PGL word: pgl27_fixed_word_coalition_distE / _content_trace_distE feed
  pgl27_exec_view_indist and pgl27_exec_trace_indist (executed 2^-39, both
  observers); pgl27_word_joint_viewE ties the joint observable to
  pgl27P_word_gen for pgl27_view_mixing (2^-40); constants unchanged.
- Transfer: var_dist_fdistmap_transfer (pgg_collusion_bound.v) +
  pgl27_word_view_indist_via_transfer re-deriving the landed 2^-39 theorem.
- den Boer: five_card_sample_cut_distE + den_boer_witness_rotationE +
  den_boer_sample_cut_witnessE re-sourced to den_boer_marginal_bound;
  five_card_exec_trace_secrecy / dealer centropy0 pair at the sample's own
  distribution.
- Kim: five_card_colour_viewE (pointwise, orientation fc_sigma ^+ k) +
  five_card_colour_view_RV_E (= kim_view) + five_card_colour_view_leak_bound
  transporting kim_input_private at exactly (eps_lt_inv5, eps_gt_neg4inv5,
  eps_small) — the stage-A split shed the parasitic Hspec/L dependence.
- Kim repeated/seven-cut: kim_repeated_cut_distE, kim_centi_witness_rhoE
  (= sw_rho_dist (scb_bound kim_security_bundle_centi), by []),
  kim_centi_cut_distE, kim_repeated_seat_distE + centi instance — endpoint
  marginal bounds, labelled as such everywhere.

## 7. Probe record and NEEDS-PROBE outcomes (§20 items 7, 17)

probe-ledger.md (committed) holds per-unit paths, build commands, timings,
mutation results with harvested errors, and Print Assumptions. The four
NEEDS-PROBE items all resolved GO with design corrections folded at §16.4:
PGL finite reader (no seat transport needed), five-card colour view
(orientation fc_sigma ^+ k; decode_bool stuck under vm behind idP — compute
on the ViewA side), transfer theorem (Hideal removal makes the conclusion
provably FALSE — semantic counterexample), facade/manifest mechanics
(module namespacing; Require-Export vocabulary vs Require-Import instances;
levels cumulative from witnesses).

## 8. Print Assumptions (§20 item 8)

Closed under the global context: pgl27_exec_correct, five_card_exec_correct,
pgl27_observed, five_card_observed, den_boer_observed (+ recovery
corollaries), pgl27_exec_rowE, profile_k_* family, five_card_exec_procs_biasE.
Boolp trio exactly (propositional_extensionality,
functional_extensionality_dep, constructive_indefinite_description), nothing
else, on every distribution-level export: the five witness ties, all cut/seat
/coalition/content-trace distEs, both executed 2^-39 bridges,
pgl27_word_joint_viewE, colour-view family incl. the Kim MI transport,
var_dist_fdistmap_transfer + PGL instantiation, and the two facade
spot-checks (PGL27Analysis.exec_view_indist,
FiveCardAnalysis.colour_view_leak_bound). No new Axiom/Admitted/Abort
anywhere (the star file's pre-existing Admitted is unbuilt and untouched
beyond its textual migration).

## 9. Files, commands, deviations (§20 items 9-10)

Files: see the four implementation commits' stats (41 changed; new:
pgg_observed_execution.v, five_card_models.v, pgl27_models.v,
pgl27_analysis.v, five_card_analysis.v, manifest/pgg_analysis_manifest.v,
manifest/pgg_analysis_client.v; _CoqProject gains 7 file lines + the
manifest -R root). Build: `make -j1` throughout, one rocqworker; full tree
green at every commit. Audit: every commit through the rocq-audit gate
(two blocked attempts fixed forward: 11 role-tag/Naming sites after T2,
2 H002 tag-kind fixes after T3-T5; zero bypasses).

As-built deviations from the plan (all recorded when made): T1+T2 edited in
one session with a single cone rebuild, committed in two slices; T3-T5
executed as one verified batch, one commit; SampleAdapter's R became
explicit at type ascriptions (record parameter inference lost with the
R-free mp — three instance sites updated); five-card facade alias
security_bound renamed endpoint_bound (enforces §13.5's own labelling
rule); probe-only vacuity declarations remain probe evidence, with the
hypothesis-consumption table as the models file's header; PGL
observed_correct alias omitted (no instance corollary landed; generic
OE.oe_run_correct noted instead).

## 10. Deferred field splits (§20 item 11)

rp_content, pi_starts_uniq, the ep_players_bridge dependent-index redesign:
recorded, not implemented (request §8; live consumers enumerated in
migration-inventory.md).

## 11. Section 3 prerequisite migration status (§20 item 12)

All Section 3 landed results preserved: the generic exec_dealer_trace,
fdistmap_prodr, sa_joint_dist unchanged; pgl27_sample_cut_distE,
pgl27_word_sample_coalition_distE, pgl27_word_cut_distE,
pgl27_word_sample_joint_distE re-typed only (R-free plug);
five_card_sample_cut_distE, the input-row pair, the dealer-row family, and
den_boer_witness_rotationE / den_boer_sample_cut_witnessE re-sourced to
den_boer_marginal_bound with proof scripts unchanged modulo the unfold-name
swap. Supporting declarations: five_card_card_bool2 kept (five_card_exec.v's
own local certificate), five_card_sample_uniform_prodE /
five_card_sample_snd_uniformE / five_card_exec_traces_size /
five_card_exec_input_trace / dealer trio / fdistmap_head1 /
rho_from_words_weighted1 / kim_weight_uniform_at0 all preserved;
five_card_exec_procs_biasE restated as the degenerate self-equality with
the bias-independence content recorded as moved into the type (flagged:
deletion is defensible if a future review prefers it).

## 12. Phase H2 inventory (§20 item 21)

7 MonodromyProfile values: 5 direct (abel, five_card, pgl27, s5, s5x5),
den_boer wrapper (live), kim wrapper (deleted). Order: (1) den Boer rows
already fold into the five-card facade; (2) s5, s5x5 facades at their
actual levels (Algebraic only — no plug, no adapter; sections 2-7
documented empty); (3) abelian recorded in the manifest, not facaded
(outside instance scope); (4) oc, monster, cyclic, star not facade-eligible
(no profile; star unbuilt with a pre-existing Admitted). No H2 step may
manufacture proofs to raise a level.

## 13. Observers, hypotheses, manifest (§20 items 13, 16, 18-20)

Observer table: section 13 of the draft retained verbatim — participant,
coalition, input-party (constant-conditioning, not privacy), dealer
(centropy0 pair), verifier (new twin), decoded colour view (seat indices
into the endpoint list), PGL finite content trace — each with its carrier
and theorem, in the facades' Observers sections with distinct types.

Hypothesis sets (item 16): kim_weight_dist/kim_input_dist need
(eps < 1/5, -4/5 < eps); the Kim MI bridge needs + eps_small
(0 < 1/5 - |eps|, kim_input_privacy.v:420 — confirmed required, witness
eps = -1/2); fc_kim_security_bound needs + |eps| < 4/5 and L; the program
layer needs NONE (parameterless closed terms). All jointly satisfiable at
eps = 0 and eps = 1/100 (probe D1 §15.7).

Manifest (items 18-20): pgg-smc/manifest/pgg_analysis_manifest.v — five
analysis paths: PGL exact-uniform (Security-bridged: exact privacy at the
executed coalition observer + conditional entropy at the trace observer),
PGL finite-word (Security-bridged: approximate privacy 2^-39 at BOTH
executed observers, joint proximity 2^-40, transfer derivation), five-card
uniform (Security-bridged: trace privacy at the executed content trace over
the sample's own distribution; dealer determination; input-row constant
conditioning listed as conditional entropy, never privacy), five-card
single-biased (Security-bridged: mutual information at colour_view under
kim_input_dist), five-card repeated + seven-cut (Sampled: endpoint marginal
bound, explicitly NOT Security-bridged). One capability line per (theorem,
distribution, observer, notion); 89 checker lines pin every alias with a
spelled type; the client compiles with exactly one import and Fail-Checks
prove instance internals stay qualified-only. Facade paths:
instances/pgl27/pgl27_analysis.v (Module PGL27Analysis, 42 aliases),
instances/kim2025/five_card_analysis.v (Module FiveCardAnalysis, 47).

## 14. Unused aliases removed (§20 item 14)

five_card_witness_cut_dist, kim_profile (repeated usage audits);
pgl27_witness_cut_dist inlined; bound_of_witness / bundle_of_witness never
shipped (probe scaffolding only).

## 15. Migration matrix (§20 item 15)

migration-matrix.md + the §16.2 audit's per-file table, with the §16.4
gap rows executed: the five profile_k_* restatements, pgl27_run.v's two
corollaries, the manifest root relocation, and the framework-internal
constructor/application sites. The final grep sweep returns zero
occurrences of any removed name in pgg-smc.

## 16. Strongest paper-facing claim now supported

> One algebraic program profile and one execution plug — both closed terms
> carrying no real-number, bias, or word-length parameter — determine the
> shared piSMC run and its executed observations, packaged with termination,
> endpoint-count, and recovery facts in a single ObservedExecution value per
> protocol. Several probability models attach to that same executable
> program: the uniform and 200-letter-word PGL models with their
> fixed-secret variants, and the uniform, single-biased, repeated-biased,
> and seven-cut five-card models. Explicit bridge theorems connect each
> featured model to its existing analysis at the executed observation:
> exact coalition-view independence and 2^-39 word-shuffle
> indistinguishability for PGL (view and content-trace observers), exact
> trace secrecy and dealer-row determination for den Boer, and the
> O(eps^2) conditional-mutual-information bound for Kim's biased cut, with
> a reusable exact-to-finite transfer theorem re-deriving the 2^-39 bound.
> One typed manifest exposes program, execution, observers, models,
> correctness, security, and transfer for each path without erasing their
> distinct types, and its five completion levels are each witnessed by
> compile-checked aliases.

Nearby claims that remain FALSE and must not be made: filling a profile
does not prove security for any shuffle or observer; the repeated and
seven-cut five-card paths have endpoint marginal bounds only (no coalition,
trace, or CMI theorem); the input-row equality is constant conditioning,
not commitment privacy; execution correctness is never security; raw seq
traces have no distributions; ts_private is a compatibility property, not
distributional privacy.

## 17. Shinagawa 2021 AFTER scorecard

`baseline-shinagawa21-after.md` (beside the BEFORE file): V1 1, V2 1, V3 1,
V4 1, V5 1, V6 0, V7 1, V8 2 — TOTAL 8/16 from 5/16. The remaining
distance is mapped: H2 facades (V2), scope README + retired-instance build
cleanup (V6, user decision), framework-header pointer refresh (V7),
cross-instance name unification (V4), directory hygiene (V5's second
point). None of these requires new mathematics.
