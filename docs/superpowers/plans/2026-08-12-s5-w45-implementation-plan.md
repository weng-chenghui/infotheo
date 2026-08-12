# Implementation plan: S5-1, S5-2, W4, W5 (+C9)

Date: 2026-08-12.

Upstream: spec `docs/superpowers/plans/2026-08-12-s5-w45-sample-law-input-trace-spec.md`
as amended (`4a7c7a4f`) after the probe and the two adversarial audits. Source
code for every task is compiled probe code — ported and renamed, not
rewritten:

- `docs/superpowers/probes/2026-08-12-s5-w45/probe_a_laws.v` (C1-C8),
- `docs/superpowers/probes/2026-08-12-s5-w45/probe_c_witness_rotation.v`
  (C9a with its three helpers; the soundness audit's compiled refutation of
  the original invariant 3, preserved from its scratchpad),
- `probe_b_mutation.v` (red file; amended in P0).

Execution: `rocq-prover` subagents at `model: opus`, one at a time, one
rocqworker; every commit passes the audit gate unbypassed; since gate
Stage 2 is the known S998 silent no-op, a real `rocq-auditor` review is
dispatched for every substantive commit (read-only, may overlap the next
stage's compile). Probe files are never edited after P0. No landed statement
is modified anywhere; all edits are additive.

## P0 — probe amendments, then probe commit

Agent task (small): amend `probe_b_mutation.v` — replace the type-error
mutation M1 with a semantic one that typechecks and must fail
(`fdistmap (fun ab : A * B => (ab.1, g ab.2)) (Pa `x Q) = (fdistmap g Q `x Pa)%fdist`);
add M4 and M5 as POSITIVE refutations where possible: search
`five_card_leakage.v` for the landed value of `` `H `p_ (Secret R) ``
(the `2 - (3/4) * log 3` entropy) and derive
`` `H( Secret R | probe_input_view j ) != 0 `` from `probe_C7` and
`` `H( Secret R | probe_dealer_view ) <> `H `p_ (Secret R) `` from
`probe_C8b`; fallback per mutation: `Fail`-guarded proof attempt + `Abort`
with a one-line comment (probe_b is the designated red file; `Abort` is
banned only in probe_a). Amend `probe_a_laws.v` ONLY by appending the
audit-F15 instantiation check: an `Example` applying `probe_C6` at
`den_boer_eps0_lt/gt/spectral` witnesses and `L = 1`. Recompile both files
(same `-R` invocation as before). probe_c is evidence, untouched.

Then (orchestrator): `git add` the probe directory sources and commit —
one commit, message citing the spec. If Stage 1 of the gate fires on probe
H-tags or naming, add the minimal missing `@intent`/`@composes` lines to the
probe files (comment-only edits) rather than bypassing.

## P1 — the generic files (one commit)

`pgg-smc/protocol/pgg_execution_plug.v`, appended to the extractor family
(mirror of `exec_input_trace`, the spec's one unprobed construction step;
fallback: drop it and keep the P3 definition local):

```coq
(** exec_dealer_trace — the executed trace of the dealer.
    @intent: entry exec_dealer_id of exec_run.2. *)
Definition exec_dealer_trace (x : ep_inputT e) (w0 : pgg_gT (mp_M mp)) :=
  nth [::] (exec_run x w0 P_idx).2 exec_dealer_id.
```

(Adapt the argument list to the section's actual parameters — read
`exec_input_trace` at `pgg_execution_plug.v:189-193` and copy its shape
exactly.)

`pgg-smc/security/pgg_sample_adapter.v`: `fdistmap_prodr` in a small generic
section before the record (probe text verbatim, `probe_` prefix dropped):

```coq
Lemma fdistmap_prodr (A B C : finType)
    (Pa : R.-fdist A) (Q : R.-fdist B) (g : B -> C) :
  fdistmap (fun ab : A * B => (ab.1, g ab.2)) (Pa `x Q)
  = (Pa `x (fdistmap g Q))%fdist.
Proof.
apply/fdist_ext => -[a c].
rewrite fdistmapE fdist_prodE fdistmapE.
rewrite (eq_big (fun a0 : A * B => (a0.1 == a) && (g a0.2 == c))
                (fun a0 : A * B => Pa a0.1 * Q a0.2)); first last.
- by move=> i _; rewrite fdist_prodE.
- by case=> x y; rewrite !inE.
rewrite (reindex_onto (fun b : B => (a, b)) snd) /=;
  last by case=> x y /andP[] /= /eqP -> _.
rewrite big_distrr /=; apply: eq_bigl => j.
by rewrite !eqxx andbT andTb.
Qed.
```

and `sa_joint_dist` beside `sa_cut_dist` (`:156`), completing layer 3:

```coq
(** sa_joint_dist — the joint distribution of the run argument and the cut.
    @intent: the pushforward of sa_sampleP along u |-> (sa_arg u, sa_cut u). *)
Definition sa_joint_dist : R.-fdist (ep_inputT e * pgg_gT (mp_M mp)) :=
  fdistmap (fun u => (sa.(sa_arg) u, sa.(sa_cut) u)) sa.(sa_sampleP).
```

(Adapt field-access syntax to the file's section idiom; the probe showed
dot-projection is required under primitive projections.) Both carry the
spec's tags: `fdistmap_prodr` `@main architecture:`, `sa_joint_dist`
`@intent:`.

Verify: `make -f Makefile.coq -j1 pgg-smc/security/pgg_sample_adapter.vo
pgg-smc/instances/pgl27/pgl27_exec.vo pgg-smc/instances/kim2025/five_card_exec.vo`
(the cone rebuild — `pgg_execution_plug.vo` rebuilds first via the
dependency graph; landed files must recompile UNCHANGED). Commit; dispatch
auditor.

## P2 — pgl27_exec.v (one commit)

Three additions, probe statements with production names and the section's
implicit `R`/`mpP` restored (re-wrap to 80 columns — production names are
up to 25 characters longer than probe names):

| Production name | Probe source | Placement |
|---|---|---|
| `pgl27_sample_cut_distE` (`@main architecture:`) | `probe_C2` (probe_a:75-82) | exact block, after `pgl27_sample_witness_prodE` (:370) |
| `pgl27_word_sample_coalition_distE` (`@main architecture:`) | `probe_C1` (probe_a:61-66) | word block, after `pgl27_word_sample_seat_distE` (:457) |
| `pgl27_word_sample_joint_distE` (`@main architecture:`) | `probe_C5_sa` (probe_a:178-188), restated as `sa_joint_dist (pgl27_word_sample secretP) = pgl27P_word_gen secretP`; the proof unfolds `sa_joint_dist` then follows probe_C5_sa's rewrite chain to `exact: fdistmap_prodr` | word block, after `pgl27_word_cut_distE` (:468) |

Only ONE C5 export lands (naming audit §22.1); the probe's raw-pair-map twin
does not.

Verify: `make -f Makefile.coq -j1 pgg-smc/instances/pgl27/pgl27_exec.vo`;
`rocq_assumptions` on the three names (boolp trio only). Commit; dispatch
auditor.

## P3 — five_card_exec.v (one commit, the big stage)

Imports: add what probe_a/probe_c needed beyond the file's current block —
`den_boer_profile` if not already imported, and for the C9 helpers
mathcomp `matrix` + infotheo `ssralg_ext` (row-vector notation
`v ``_ ord0`, `\row_`) with `Local Open Scope vec_ext_scope` scoped to the
one-letter section. If an import triggers a notation-scope conflict with the
landed proofs (the repo's known pismc/classical_sets hazard class), isolate
the C9 helpers in a trailing section with `Local` opens and report.

Inside `Section five_card_execution` (before `End` at :535), in ledger
order; probe sources with production names per the spec's ledger table:

| Production name | Probe source |
|---|---|
| `five_card_card_bool2` (`@composes: five_card_sample_uniform_prodE`; `Naming:` line documenting the deliberate local duplicate of `kim_input_privacy.card_bool2`) | `probe_card_bool2` (probe_a:90-91) |
| `five_card_sample_uniform_prodE` (`@composes: five_card_sample_snd_uniformE`) | `probe_omega_prodE` (probe_a:96-104) |
| `five_card_sample_snd_uniformE` (`@composes: five_card_sample_cut_distE`) | `probe_omega_snd_uniform` (probe_a:109-115) |
| `five_card_sample_cut_distE` (`@main architecture:`) | `probe_C3` (probe_a:121-129) |
| `five_card_exec_traces_size` (`@composes: five_card_exec_input_raw_traceE`; `Naming:` per :166-167 template) | `probe_run_traces_size` (probe_a:204-206) |
| `five_card_exec_input_raw_traceE` (`@composes: five_card_exec_input_trace_secrecy`; comment splits the two reasons per invariant 6) | `probe_C6` (probe_a:210-219) |
| `five_card_exec_input_trace` Definition (`@intent:`; `Naming:` line) | `probe_input_view` (probe_a:229-231) |
| `five_card_exec_input_trace_secrecy` (`@main architecture:` — NOT security; the invariant-2 caveats (i)-(iv) INSIDE the rendered comment; `Naming:` line) | `probe_C7` (probe_a:236-245) |
| `five_card_exec_dealer_raw_trace` Definition via the P1 generic `exec_dealer_trace` (fallback: the probe's local `nth`-form verbatim) (`@intent:`; `Naming:` line) | `probe_exec_dealer_trace` (probe_a:254-256) |
| `five_card_exec_dealer_raw_traceE` (`@composes: five_card_exec_dealer_traceE`; comment states the row is anti-chronological: head = the dealer's own Init of the deck index, then party 8's sheet, then party 7's — audit F9 wording) | `probe_C8a` (probe_a:262-269) |
| `five_card_exec_dealer_readout` Definition (`@intent:`; comment notes the `(false, false)` default coincides with a legitimate pair, so the readout is meaningful only through `five_card_exec_dealer_raw_traceE`; `Naming:` line) | `probe_dealer_readout` (probe_a:274-277) |
| `five_card_exec_dealer_trace` Definition, `{RV dbP -> bool * bool}` (`@intent:`; `Naming:` line) | `probe_dealer_view` (probe_a:283-285) |
| `five_card_exec_dealer_traceE` (`@composes: five_card_exec_dealer_pair_centropy0`) | `probe_C8b_fun` (probe_a:289-293) |
| `five_card_exec_dealer_pair_centropy0`: `` `H( (fun w : five_card_leakage.Omega => w.1) | five_card_exec_dealer_trace ) = 0 `` — rewrite `five_card_exec_dealer_traceE`, then `centropy_RV_comp0` at `f := id` (`@main security:`; `Naming:` line) | new one-liner (audit F8), from probe_C8b_fun |
| `five_card_exec_dealer_trace_centropy0` (`@main security:`; `Naming:` line) | `probe_C8b` (probe_a:297-303) |

After `End five_card_execution`, standalone in the
`five_card_exec_procs_biasE` style (probe_c sources verbatim, section
wrappers adapted; helper names kept):

| Production name | Probe source |
|---|---|
| `fdistmap_head1` (`@composes: rho_from_words_weighted1`) | probe_c:27-37 |
| `rho_from_words_weighted1` (`@composes: den_boer_witness_rotationE`) | probe_c:39-48 |
| `kim_weight_uniform_at0` (`@composes: den_boer_witness_rotationE`) | probe_c:55-61 |
| `den_boer_witness_rotationE` (`@composes: den_boer_sample_cut_witnessE`) | probe_c:65-71 (`denboer_witness_is_rotation`) |
| `den_boer_sample_cut_witnessE` (`@main architecture:`): `forall (R : realType) eps Hlt Hgt Hspec L, five_card_sample_cut_dist Hlt Hgt Hspec L = sw_rho_dist (mp_security (den_boer_profile R))` — proof: `by rewrite five_card_sample_cut_distE den_boer_witness_rotationE.` | the one unprobed derivation (two-rewrite chain of two compiled facts). Contingency: if the rewrite chain resists (argument-form mismatch on `five_card_sample_cut_dist` outside the section), state it at the `den_boer_eps0_*` witnesses only and record the narrowing in the as-built |

The C9 helpers live here, not in `pgg_weighted_words.v`, because editing
that file would invalidate the entire downstream `.vo` cone for two
consumers-of-one lemma (rebuild-cost decision, recorded).

Verify: `make -f Makefile.coq -j1 pgg-smc/instances/kim2025/five_card_exec.vo`;
`rocq_assumptions` on `five_card_sample_cut_distE`,
`five_card_exec_input_raw_traceE`, `five_card_exec_input_trace_secrecy`,
`five_card_exec_dealer_pair_centropy0`,
`five_card_exec_dealer_trace_centropy0`, `den_boer_sample_cut_witnessE`
(boolp trio only). Commit; dispatch auditor.

## P4 — close-out

1. `/rocq:golf`-style pass, proof bodies only, on the four touched files'
   NEW proofs (expect near-zero — the ported bodies are probe-minimal;
   report the measured figure honestly). Re-verify assumptions after.
2. As-built record appended to THIS plan: stage/commit table, deviations
   verbatim, final assumption state.
3. Memory update (`project_monodromy_profile_evaluation.md` gains the
   S5/W4/W5 landing paragraph; MEMORY.md index line amended).

## Verification inputs (per the test-material rule)

Every stage's verification input is named probe code: P1/P2/P3 statements
are ports of `probe_a_laws.v`/`probe_c_witness_rotation.v` (compiled at
`e1c1f884`-era sources, re-verified by the soundness audit on the built
`.vo`); the mutation evidence is `probe_b_mutation.v` post-P0; the landed
files recompiling unchanged in P1's cone rebuild is the no-regression
check.

## Gate

Estimated ~260 lines of ported Rocq across 4 commits (P0 probes, P1-P3),
plus the close-out. The only unprobed items: the `exec_dealer_trace`
parameterization (P1, fallback recorded) and the `den_boer_sample_cut_witnessE`
two-rewrite derivation (P3, contingency recorded).

## As-built record (executed 2026-08-12 on user go)

All stages executed; every commit passed the gate unbypassed (the gate's
Stage 2 was the known S998 silent no-op on each, so a real `rocq-auditor`
review was dispatched per commit; all four returned PASS at error severity).

| Stage | Commit | Outcome |
|---|---|---|
| P0 | `ea0500f2` | probe_b: semantic M1 + POSITIVE M4/M5 (via `H_secret` at `five_card_leakage.v:86` and a new `mut_secret_entropy_gt0 : 0 < H` bound through `log4`/`ltr_log`); probe_a: F15 instantiation Example appended; both green. Probe-commit audit PASS (probes are `excluded_paths` for the rule catalog; manual honesty check clean) |
| P1 | `2376b3bd` | `exec_dealer_trace` + `fdistmap_prodr` + `sa_joint_dist`; cone rebuilt, instance files recompiled unchanged. Audit PASS, one advisory (header-table "law" wording matches its pre-existing sibling lines; kept for local consistency) |
| P2 | `74726029` | The three pgl27 exports. Audit PASS; C5 deep-check confirmed the single-export rule and the honest instantiation of the P1-deviated `sa_joint_dist` |
| P3 | `c4f159b2` | All fifteen Part-A items + five Part-B items (+329/-2). C9b landed at FULL generality — the contingency was unused. Audit PASS; invariant-2 caveats verified verbatim in the rendered comments |
| Golf | `78e8b8d9` | Bodies only, measured -6 lines (-0.7%), saturation: 3 of 24 candidates shortened (notably `fdistmap_head1` via `bigop_ext.big_rV1_ord0` replacing a hand-rolled `big_pred1` argument). All 17 `@main` exports of `five_card_exec.v` re-verified boolp-trio-only |

Deviations from the written plan, verbatim intent preserved:

1. P1: the plan's literal `sa_joint_dist` was ill-typed (`ep_inputT : Type`
   is not a finType; the probe only exercised the instance where it
   delta-reduces). Landed form parameterizes the argument reader:
   `sa_joint_dist (argT : finType) (arg : sa_sampleT sa -> argT)`. C5's
   landed statement `sa_joint_dist (pgl27_word_sample.(sa_arg)) =
   pgl27P_word_gen secretP` is the honest instantiation (auditor-confirmed).
2. P0: the plan's swapped-factor M1 was ill-typed across distinct carriers;
   landed at a single carrier `A` where it typechecks and is refuted
   positively via `fdist1` witnesses.
3. P3: minor reflows and qualification matched to the file (`P R`
   unqualified, `unit_RV dbP`); item 14 needed the pair split by cases
   (`prod` has no definitional eta) before `centropy_RV_comp0` at
   `f := idfun`.

Independent final verification (orchestrator, own compile): the ten cycle
exports — `fdistmap_prodr`, `pgl27_sample_cut_distE`,
`pgl27_word_sample_coalition_distE`, `pgl27_word_sample_joint_distE`,
`five_card_sample_cut_distE`, `five_card_exec_input_raw_traceE`,
`five_card_exec_input_trace_secrecy`,
`five_card_exec_dealer_pair_centropy0`,
`five_card_exec_dealer_trace_centropy0`, `den_boer_sample_cut_witnessE` —
each depend on exactly the boolp trio (10/10 `Print Assumptions` blocks);
zero `Admitted`/`Abort`/`Axiom` in the four touched files; gate run
recorded for every commit including golf (`20260812T021805Z-9c02d610-d9c2`,
clean). Probe directory frozen at `ea0500f2` (+ the pre-existing frozen
2026-08-11 directory untouched).

Notes for future cycles: `.git/hooks/pre-commit` is NOT installed in this
clone — the gate fires only through the Claude Code hook, so commits made
outside Claude Code skip the audit; installing via
`.claude/audit/bin/install-hooks.sh` is a one-line fix awaiting a user
decision.

Post-cycle sweep (user go 2026-08-12): the P2 auditor's candidate
"law" -> "distribution" terminology sweep landed as `5439a34e` — comment
prose only, across `pgg_sample_adapter.v`, `pgl27_exec.v`,
`five_card_exec.v` (`pgg_execution_plug.v` had no occurrences); the
identifier `sa_seat_dist_law` and its name references stay per the
identifiers-exempt rule; all lines re-wrapped within 80 columns; the
three-file cone rebuilt clean with one rocqworker; gate run
`20260812T031938Z-6bbb2f2d-6ca6` clean (Stage 1 re-validated every touched
entity's comment tags; no semantic review dispatched — no statement or
proof term changed).
