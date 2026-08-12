# Implementation plan: layered protocol packing (stages A-H1)

Date: 2026-08-12. Authorized by the §16.4 record of the request
(`docs/superpowers/requests/2026-08-12-layered-protocol-packing-ROCQ-formalization-request.md`):
probe gate green (units A-F), soundness audit GO, API/naming audit GO.
Probe sources under `docs/superpowers/probes/2026-08-12-layered-protocol-packing/`
are the VERBATIM sources for every record, statement, and proof shape below;
per-task citations name the probe file. Build discipline: `make -j1` only,
one rocqworker; never `rewrite !` with arithmetic lemmas; no `lia` in new
code; the three catalogued lazy-eval bombs and their guards (probe ledger)
are standing rules. Every task is one commit; the tree compiles green before
the next task starts. This document becomes the as-built record: every
deviation is recorded in place.

## Decisions already made (no implementation judgment remains)

| # | Decision | Reason |
|---|---|---|
| D1 | Migration is additive-then-flip in exactly two cone rebuilds: T1 (small additive, pgg_collusion_bound.v) then T2 (the atomic flip) | minimizes full-cone rebuilds; §5.2 mandates atomicity for the witness swap |
| D2 | `bound_of_witness`/`bundle_of_witness` do NOT ship; new values apply the new constructors to the same arguments the old `MkSecurityWitness` took | §16.4 item 7 |
| D3 | New records carry the four `Arguments` lines of probe B verbatim; `ObservedExecution` lives in `Module OE` under `Unset Implicit Arguments` | §16.4 item 5 |
| D4 | Instance OE values live in the instance exec files (framework files never import instance files — depgraph invariant) | 2026-08-11 probe G |
| D5 | New model files: `instances/kim2025/five_card_models.v`, `instances/pgl27/pgl27_models.v` (keeps the exec files' import cones untouched; five_card_models imports kim_input_privacy which five_card_exec.v does not) | probe D1 finding 6 |
| D6 | Facades: `instances/pgl27/pgl27_analysis.v` (`Module PGL27Analysis`), `instances/kim2025/five_card_analysis.v` (`Module FiveCardAnalysis`); `Require Export` framework vocabulary, `Require Import` instance cone | §16.4 item 2; probe F visibility finding |
| D7 | Manifest + client in new root `pgg-smc/manifest/` with `-R pgg-smc/manifest pgg_smc` | §16.4 item 4 |
| D8 | Transfer lemma home: `pgg_collusion_bound.v` (`var_dist_refl`, `var_dist_fdistmap_transfer` + `Arguments : clear implicits`); PGL instantiation in `pgl27_models.v` | §16.4 item 6 |
| D9 | Instance value names: `pgl27_marginal_bound`, `pgl27_certificate_bundle`, `fc_kim_security_bundle`, `kim_security_bundle_centi`, `den_boer_marginal_bound` | §5.2 + §16.4 item 8 |
| D10 | `five_card_witness_cut_dist` deleted; `pgl27_witness_cut_dist` inlined into `pgl27_sample_cut_distE` | probe B usage audit |
| D11 | `kim_profile` wrapper deleted (orphaned; zero references) | inventory + probe F H2 |
| D12 | `five_card_exec_procs_biasE` restated as the degenerate self-equality over the single parameterless plug, with a comment recording that the bias-independence content moved into the type | audit table row |
| D13 | Some-shape facts use `isSome` or `= Some/None` equations, never `!= None` | probe B API fact |
| D14 | Facade retention checks: spelled type ascriptions only; value-level `erefl` checks only for the two program-layer aliases; everything Timeout-guarded | probe F bomb 3 |
| D15 | Manifest levels computed cumulatively from witnessed aliases; capabilities one line per (theorem, distribution, observer, notion) | §16.4 item 1 |

## T1 — transfer lemmas into pgg_collusion_bound.v

Copy from `probe_e_transfer.v`: `var_dist_refl` (with `@composes:` tag) and
`var_dist_fdistmap_transfer` verbatim (Section binders, proof:
le_trans/var_dist_triangle, lerD, var_dist_fdistmap ×2, symmetric_var_dist;
`@main architecture:` tag), plus `Arguments var_dist_fdistmap_transfer : clear implicits.`
Verify: `make -j1` the cone; `Print Assumptions` = boolp trio. Commit.

## T2 — the atomic flip (stages A + B + C comments)

One commit across the files below. Execution order inside the task follows
`_CoqProject` dependency order; the compile loop is incremental `make -j1`.
Sources: `probe_a_profile_split.v` module PS (all record/API shapes and the
instance plug/profile bodies, verbatim), `probe_b_witness_split.v` (records,
Arguments, constructor migrations, consumer patterns, the five tie proofs).

1. `reconstruct/algebraic_rigidity.v`: delete `SecurityWitness`; add
   `ShuffleMarginalBound`/`ShuffleCertificateBundle` + 4 Arguments lines +
   `shuffle_bundle_of_bound`; migrate `security_witness_fiber`,
   `security_witness_endpoint_inj`, `security_witness_from_bound` → return
   `ShuffleMarginalBound`; `security_witness_with_exact` → bundle (EXACT);
   `ar_security` → bundle; `sp_witness`/`cs_witness` → bound;
   `certified_from_witness` → `certified_from_bound` (takes bound);
   `ar_security_profile` projects `scb_bound`. §14.2 comments on `sw_*`,
   `scb_*` (marginal-only scope; optional attachments; what `sw` stands for).
2. `protocol/pgg_monodromy_profile.v`: record drops `R` + `mp_security`;
   delete `profile_eps`, `profile_anonymous`; section loses `R`; §14.2
   comments on all four fields; header updated (no security claim; current
   in-scope fillers named).
3. `protocol/pgg_execution_plug.v`: record drops `R` + `ep_cards_bridge`;
   smart constructors lose both; delete `exec_content_from_plug`; derived
   API loses `R` (bodies unchanged); add `exec_verifier_trace` +
   `exec_endpoints_verifier_traceE`; §14.2 comments on the seven fields and
   five extractors (observer-scope comments per §7.8).
4. `security/pgg_sample_adapter.v`: `mp`/`e` re-typed (R stays on the
   record); five generic `@exec_*` sites drop `R`; §14.2 comments on the
   four fields + `sa_joint_dist` finite-reader comment.
5. `security/pgg_schreier.v` (ASYM bundle), `security/pgg_entropy_security.v`
   (bound), `security/pgg_uniform_security.v` (EXACT bundle),
   `security/pgg_security_solver.v` + `security/pgg_collusion_bound.v`
   (comment updates), `security/pgg_entropy_security_demo.v` (4 bound
   producers + eps lemmas re-typed).
6. `reconstruct/combinatorial_rigidity.v` (`cr_security` → bundle),
   `reconstruct/pgg_dealer_bridge.v` (+`scb_bound` projections),
   `reconstruct/pgg_protocol_landscape.v` (8 sites incl.
   `security_per_position` at bound, `discovery_to_certification` → bundle),
   `reconstruct/pgg_landscape_demo.v` (6 projection sites).
7. Instances — witnesses: pgl27 (`pgl27_marginal_bound` +
   `pgl27_certificate_bundle`), kim2025 (`fc_kim_security_bundle`,
   `kim_security_bundle_centi`, `kim_deal_centi_lt` through `scb_bound`,
   `five_card_eps0_eq0` re-typed), s5/s5x5/oc/monster/abelian/cyclic (fiber
   → bound; schreier → ASYM bundle; rigidity values via
   `shuffle_bundle_of_bound` or the schreier bundles), star (same edits,
   not built — best effort, non-gating).
8. Instances — profiles: `pgl27_profile`, `s5_profile`, `s5x5_profile`,
   `abel_profile` lose `R` + witness arg; `five_card_profile` becomes the
   PARAMETERLESS closed term; `den_boer_profile := five_card_profile`;
   `kim_profile` deleted (D11); `profile_k_pgl27/_s5/_s5x5/_abel/_denboer`
   restated without `R`; `profile_eps_pgl27` restated as
   `sw_bound_eps pgl27_marginal_bound = 0`; `den_boer_perfect` restated over
   `den_boer_marginal_bound := scb_bound (fc_kim_security_bundle eps0-pack 1)`
   — probe B proof shapes verbatim.
9. `instances/pgl27/pgl27_run.v`: `run_recover_pgl27`/`run_party_pgl27`
   statements drop `R`. `instances/pgl27/pgl27_group.v`: comment update
   (the Notation constraint now cites ShuffleMarginalBound).
10. `instances/pgl27/pgl27_exec.v` (24 `@exec_*` sites drop R; plug ctor;
    `pgl27_witness_cut_dist` inlined; `pgl27_sample_witness_prodE` +
    `pgl27_sample_cut_distE` against `pgl27_marginal_bound`) and
    `instances/kim2025/five_card_exec.v` (30 sites; plug ctor; section
    loses eps/hypotheses/L for the execution half — sample half keeps R;
    `five_card_witness_cut_dist` deleted; `den_boer_witness_rotationE`/
    `den_boer_sample_cut_witnessE` against `den_boer_marginal_bound`;
    `five_card_exec_procs_biasE` per D12). Grep-driven checklist: every
    `@exec_`, `@run_`, `@sa_`, `MkExecutionPlug`, `MkSampleAdapter`,
    `mp_security`, `sw_exact`, `sw_asymptotic`, `SecurityWitness` site
    must be visited; the commit is complete when all greps return only
    new-form hits.
Verify: full `make -j1`; `Print Assumptions` on `pgl27_exec_correct`,
`five_card_exec_correct` (expect closed), the five ties (boolp trio);
grep sweeps zero for `SecurityWitness|MkSecurityWitness|mp_security|ep_cards_bridge|exec_content_from_plug|profile_eps|profile_anonymous`
in pgg-smc. Commit.

## T3 — ObservedExecution (stage D)

New file `protocol/pgg_observed_execution.v` (after pgg_execution_plug in
`_CoqProject`): `Module OE` + `Unset Implicit Arguments` + the §9 record +
the five one-line derivations + five extractor specializations — from
`probe_c_observed_execution.v` verbatim (drop the PS prefix; the production
records now ARE the PS shapes). Instance values in the exec files:
`pgl27_observed` (pgl27_exec.v), `five_card_observed` + `den_boer_observed`
(five_card_exec.v), discharge proofs verbatim from probe C. §14.2 comments
on every oe_* field (dependency of oe_execution on oe_profile;
group-membership scope of oe_static_recon). Verify: make -j1;
Print Assumptions on both values (closed). Commit.

## T4 — five-card models and bridges (stage E five-card + Kim bridge)

New file `instances/kim2025/five_card_models.v` (imports five_card_exec,
kim_input_privacy, pgg_weighted_words): from `probe_d1_five_card_models.v`
verbatim — `kim_single_sample`, `kim_repeated_sample`,
`kim_centi_repeated_sample`; `kim_single_snd_weightE`, `kim_single_cut_distE`,
`kim_repeated_cut_distE`, `kim_centi_witness_rhoE` (now against
`scb_bound kim_security_bundle_centi`), `kim_centi_cut_distE`;
`five_card_exec_colour_view` (+ `Naming:` line, "seat indices into the
endpoint list" vocabulary), `five_card_colour_viewE`,
`five_card_colour_view_RV_E`, `five_card_colour_view_leak_bound` (post-T2
signature must discharge to exactly `eps_lt_inv5, eps_gt_neg4inv5,
eps_small` — §16.4 item 12 check), `kim_repeated_seat_distE` + centi
instance, the §15.7 vacuity section (hypothesis table as comments).
Tags: distE lemmas `@main architecture:`; leak bound `@main security:`;
`fc_kim_security_bound`-adjacent exports `@main bound:`. Commit.

## T5 — PGL models and bridges (stage E PGL + F + G instantiation)

New file `instances/pgl27/pgl27_models.v` (imports pgl27_exec, pgl27_trace,
pgl27_word_privacy, pgg_collusion_bound): from `probe_d2_pgl27_models.v` +
`probe_e_transfer.v` verbatim — `pgl27_fixed_sample`,
`pgl27_fixed_word_sample` (carrier ascription `(pgg_gT pgl27_M : finType)`),
`pgl27_fixed_cut_distE`, `pgl27_fixed_word_cut_distE`;
`pgl27_exec_content_trace` (+ Naming:), `pgl27_exec_rowE`,
`pgl27_content_traceE`, `pgl27_static_coalition_viewE`;
`pgl27_fixed_word_coalition_distE`, `pgl27_fixed_word_content_trace_distE`,
`pgl27_word_joint_viewE`; the executed bridges `pgl27_exec_view_indist`,
`pgl27_exec_trace_indist` (both `@main security:`, 2^-39 verbatim);
`pgl27_exact_coalition_distE` + `pgl27_exec_exact_view_indep` (+ Naming:);
`pgl27_word_view_indist_via_transfer` (+ Naming:). Commit.

## T6 — facades (stage H1 phase 1)

`instances/pgl27/pgl27_analysis.v` (`Module PGL27Analysis`) and
`instances/kim2025/five_card_analysis.v` (`Module FiveCardAnalysis`):
seven sections in the fixed order; aliases per probe F's inventories
RE-TARGETED to post-migration names, PLUS (§16.4 item 1): the
distribution-to-observer bridge aliases (`*_cut_distE`, `*_seat_distE`,
`*_coalition_distE`, `*_content_trace_distE`, `pgl27_exact_coalition_distE`)
in the Models or Security sections of their facade; the PGL facade exposes
`pgl27_exec_content_trace`, `pgl27_content_traceE`, and the two executed
2^-39 bridges; the five-card facade exposes `ObservedExecution` values,
the decoded colour view, and the bound sub-block (`fc_kim_security_bundle`
projections, `kim_deal_centi_lt`) under `bound` heading. Retention checks
per D14. Empty-section documentation for five-card Transfer. Verify each
facade against the §13.1 minimum list as a check table in the file header.
Commit.

## T7 — manifest + client (stage H1 phase 2)

`pgg-smc/manifest/pgg_analysis_manifest.v`: Require Export both facades;
row table with the observed-execution column FILLED (values exist post-T3);
levels cumulative per D15 (expected: PGL exact Security-bridged via the
exact bridge alias; PGL word Security-bridged at both static and executed
layers; five-card uniform Security-bridged via trace secrecy aliases wait —
levels assigned strictly from the witness table of §13.2, computed at
writing time from the aliases actually present; no level asserted in this
plan); capability lines one per (theorem, distribution, observer, notion);
checker Check-block (spelled ascriptions, Timeout 60).
`pgg-smc/manifest/pgg_analysis_client.v`: one import, reach checks.
`_CoqProject`: add `-R pgg-smc/manifest pgg_smc` +ordered entries for all
six new files; `make -j1` regenerates Makefile.conf. Verify: clean-client
build; deleting any listed alias breaks the manifest compile (spot mutation,
not committed). Commit.

## T8 — verification sweep + H2 inventory + report

Full `make -j1` from clean state of the changed cone; `Print Assumptions`
sweep on all new public theorems; grep sweeps (§14.4 vocabulary; no
Admitted/Abort/Axiom); the §20 completion report + response document
(separate file, P5); Shinagawa21 AFTER measurement; auto-memory update.
Golf pass (bodies only) only if time permits — record measured reduction.

## Verification inputs (feedback_test_material_sources)

Every task's verification input is named in place: the probe files (frozen,
committed at the gate commit), the live pgg-smc sources at HEAD 995e2a39,
and `make -j1` builds of the edited cone. No synthetic fixtures are needed;
the mutation checks were discharged at the probe gate and are not re-run
during implementation.
