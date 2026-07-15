# A rocq-mcp Usage Retrospective (tables edition)

Empirical analysis of **1997** rocq-mcp tool calls in the `infotheo-itp` project.
Corpus window 2026-05-08 to 2026-06-01. This is the diagram-free companion to
`rocq-mcp-retrospective.pdf`. Every chart in the PDF appears here as a table.

## Method note

A "call" is a transcript `tool_use` block whose name begins with
`mcp__rocq-mcp__`, joined to its `tool_result` by `tool_use_id`. Tool names
mentioned in prose are never counted. Counting only the main-thread transcripts
finds just 38 calls. Recursing into the `subagents/` directories finds 1997, a
roughly 50x correction, because 98.1% of all calls were delegated to subagents.
Every call matched a result, with 0 unmatched and 0 duplicate ids collapsed.
Per-call latency is the wall-clock gap between a call's timestamp and its result's
timestamp, so it includes harness overhead and should be read as approximate.
A failure is classified as `tool-defect`, `operator-usage`,
`legitimate-proof-state`, or `ambiguous` by a best-effort regex over the error
text, audited by sampling. The `ambiguous` bucket is left honestly large rather
than force-fitted.

## Corpus summary

| Metric | Value |
|---|---|
| Transcripts parsed | 580 (422 main, 158 subagent) |
| rocq-mcp calls (deduped) | 1997 |
| Calls on main thread / in subagents | 38 / 1959 (98.1% subagent) |
| Matched to a result / unmatched | 1997 / 0 |
| Success / failure / unknown | 1208 / 778 / 11 |
| Overall success rate (matched) | 60.8% |
| `force_restart` invocations | 80 |
| Stuck runs (>= 3 consecutive failures) | 81 (worst run 10) |

## Executive summary

- **Volume and delegation.** 1997 calls, 98.1% inside subagents, 94% under a
  single `rocq-prover` agent. The prover was driven by delegation, not by hand.
- **One tool does the work.** `rocq_check` alone is 1300 calls, 65% of all
  traffic, at a 0.024 s median. It is the iteration engine. Everything else is
  setup and search.
- **A defect disabled whole tools.** The "No node at point" positioning bug
  (coq-lsp >= 0.2.4, patched only on 2026-06-02, after this window) accounts for
  245 failures and rendered `rocq_query` (150/150) and `rocq_assumptions` (21/21)
  100% non-functional.
- **The workhorse was reliable.** `rocq_check` reached success on 66.4% of its
  calls and had essentially zero "No node" failures. Its failures are the proof
  work itself, not the tool.
- **Big files time out.** 53 timeouts, mostly `rocq_start` on large files, whose
  p90 latency is 30.1 s, right at the ceiling.
- **Two safety tools went unused.** `rocq_verify` and `rocq_notations` were never
  called, so the axiom and statement-mismatch safety net was never engaged.
- **Recovery was healthy.** The most common move after a failure was a principled
  `from_state` backtrack. Only 14 failures were truly abandoned.

## 1. Usage profile, reliability, and latency (per tool)

Replaces the tool-volume pie, the success-rate bars, and the latency chart.

| Tool | Calls | %vol | Succ | Fail | Unk | Succ% | Median (s) | p90 (s) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `rocq_check` | 1300 | 65.1 | 863 | 436 | 1 | 66.4 | 0.024 | 0.066 |
| `rocq_start` | 315 | 15.8 | 177 | 137 | 1 | 56.4 | 0.28 | 30.1 |
| `rocq_query` | 150 | 7.5 | 0 | 150 | 0 | 0.0 | 0.144 | 5.05 |
| `rocq_step_multi` | 114 | 5.7 | 102 | 3 | 9 | 97.1 | 0.05 | 0.27 |
| `rocq_compile_file` | 64 | 3.2 | 35 | 29 | 0 | 54.7 | 5.54 | 6.94 |
| `rocq_compile` | 29 | 1.5 | 27 | 2 | 0 | 93.1 | 5.24 | 6.11 |
| `rocq_assumptions` | 21 | 1.1 | 0 | 21 | 0 | 0.0 | 0.135 | 6.68 |
| `rocq_toc` | 4 | 0.2 | 4 | 0 | 0 | 100.0 | 0.157 | 0.48 |
| `rocq_verify` | 0 | 0.0 | - | - | - | - | - | - |
| `rocq_notations` | 0 | 0.0 | - | - | - | - | - | - |

The two 0% tools are not noise. Every one of their calls failed to the same
positioning defect. The latency column is the clearest validation of the intended
verification ladder: `rocq_check` returns about an order of magnitude faster than
the batch compilers, so cheap iteration genuinely was cheap. The `rocq_start` p90
of 30.1 s is the timeout cliff on large files.

**Batch exploration.** `rocq_step_multi` shows the value of non-destructive
probing. 89% of calls succeed even though only 41% of the 389 individual tactics
tried actually applied. The tool is meant to spray candidate tactics and keep the
one that sticks, and that is the observed pattern.

## 2. Calls by agent type

Replaces the agent-type pie.

| Agent type | Calls | Succ% |
|---|---:|---:|
| `rocq-prover` | 1880 | 59.9 |
| `rocq:proof-golfer` | 79 | 77.2 |
| main thread, direct | 38 | 52.6 |

## 3. Calls by session

Replaces the per-session bar chart. The auto-generated session slugs are mapped to
the topic each session actually worked on, from its plan, first prompt, and
dominant `rocq_start` file and theorem arguments.

| Topic | Calls | Succ% | Original slug |
|---|---:|---:|---|
| DSDP secrecy chain + entropy (V2-aware) | 1500 | 60.3 | `sprightly-finding-robin` |
| DSDP secrecy, PISMC variant (plan cont.) | 324 | 59.6 | `read-plan-claude-plans-sprightly-finding-vast-coral` |
| DSDP IND-CPA shell-link / trace bridge | 130 | 67.7 | `transient-juggling-flurry` |
| DSDP Charlie game-equivalence | 33 | 57.6 | `so-according-to-what-fluttering-goose` |
| main thread / misc | 5 | 20.0 | `(no slug)` |
| SMC interpreter soundness (rstep) | 5 | 40.0 | `focus-on-the-rstep-squishy-alpaca` |

Session detail:

- **DSDP secrecy chain + entropy.** DSDP Alice-secrecy: the V2-aware SSProve chain,
  concrete corollaries, and the entropy-form bound. Key theorems
  `dsdp_alice_secrecy_indcpa`, `secrecy_random_guess`. Files `dsdp_security_indcpa.v`,
  `dsdp_security_indcpa_concrete.v`, `dsdp_entropy.v`.
- **DSDP secrecy, PISMC variant.** Continuation of the secrecy plan against the
  PISMC formulation. Key theorems `game_real_eq_pismc`, `dsdp_alice_secrecy_pismc`,
  `entropy_ge_bound_pismc`.
- **DSDP IND-CPA shell-link / trace bridge.** Lemmas `valid_boolean_shell_link`,
  `log_id`, `alice_trace_eq_concrete` in `dsdp_security_indcpa.v` and
  `dsdp_trace_bridge.v`.
- **DSDP Charlie game-equivalence.** `game_real_equiv_charlie_real` and
  `valid_code_link_residual`. This session also covered merged-flow workflow planning.
- **SMC interpreter soundness.** rstep soundness port between the `dumas2017dual`
  and `itp2026-dumas2017dual` branches in `smc/smc_interpreter_sound.v`.

## 4. Error taxonomy

Replaces the error-category bar chart. Ranks the 778 failures by category.

| Error category | Count | %fail |
|---|---:|---:|
| No node at point | 245 | 31.5 |
| Other (uncategorised compile/error text) | 163 | 21.0 |
| Syntax / parse | 122 | 15.7 |
| Reference / theorem not found | 97 | 12.5 |
| Timeout | 53 | 6.8 |
| Proof-state (apply / unify / unfinished) | 49 | 6.3 |
| Focus discipline | 43 | 5.5 |
| Restart-through-Load | 5 | 0.6 |
| Notation ambiguity | 1 | 0.1 |

## 5. Per-tool error breakdown

This is the table behind the defect-versus-usage story. `rocq_check` has zero
"No node at point" failures because it works from an established proof state and is
immune to the positioning bug. `rocq_query` and `rocq_assumptions` are almost
entirely the defect.

| Tool | Fails | No node | Timeout | Syntax | Ref-not-found | Proof-state | Focus | Restart | Other |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `rocq_check` | 436 | 0 | 7 | 109 | 78 | 47 | 43 | 5 | 146 |
| `rocq_start` | 137 | 81 | 38 | 0 | 18 | 0 | 0 | 0 | 0 |
| `rocq_query` | 150 | 145 | 5 | 0 | 0 | 0 | 0 | 0 | 0 |
| `rocq_assumptions` | 21 | 19 | 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| `rocq_compile_file` | 29 | 0 | 0 | 13 | 1 | 2 | 0 | 0 | 13 |
| `rocq_step_multi` | 3 | 0 | 1 | 0 | 0 | 0 | 0 | 0 | 2 |
| `rocq_compile` | 2 | 0 | 0 | 0 | 0 | 0 | 0 | 0 | 2 |

The column set omits `Notation ambiguity`, which has a single occurrence in
`rocq_check`, so that row sums to 435 of its 436 failures. Hot-spot files for
failures were `smc/pismc_to_ssprove.v` (SSProve wiring) and
`dumas2017dual/dsdp/ref/dsdp_security_indcpa.v`.

## 6. Failure attribution (defects vs usage)

Replaces the failure-attribution pie. `legitimate` means a tactic that simply did
not close a goal, which is nobody's fault.

| Attribution | Count | %fail |
|---|---:|---:|
| tool-defect (No node 245, timeout 53, Restart-through-Load 5) | 303 | 38.9 |
| ambiguous (ref-not-found, proof-search-failed, mid-dev compile errors) | 260 | 33.4 |
| operator-usage (syntax, focus, notation) | 166 | 21.3 |
| legitimate-proof-state (apply / unify) | 49 | 6.3 |

Reading: the confidently attributable tool-defect share, 38.9%, is real and
concentrated in the setup and query tools. The confidently legitimate share, 6.3%,
is a lower bound, because much of the large `ambiguous` bucket is also ordinary
proving. The workhorse `rocq_check` is almost defect-free. One caveat trims the
defect figure: a fraction of `rocq_start` "No node" results can mean "you started
on a line with an earlier error" rather than the coq-lsp bug, so 303 is an upper
bound on genuine tool defects.

## 7. Daily activity

Replaces the timeline chart. Work was bursty, concentrated on 2026-05-13/14.

| Date | Success | Failure | Total |
|---|---:|---:|---:|
| 2026-05-13 | 490 | 352 | 842 |
| 2026-05-14 | 474 | 275 | 749 |
| 2026-05-15 | 135 | 92 | 227 |
| 2026-05-19 | 19 | 14 | 33 |
| 2026-05-22 | 15 | 0 | 15 |
| 2026-05-23 | 13 | 13 | 26 |
| 2026-05-24 | 11 | 5 | 16 |
| 2026-05-25 | 11 | 0 | 11 |
| 2026-05-28 | 38 | 24 | 62 |
| 2026-06-01 | 2 | 3 | 5 |

## 8. Recovery and friction

The call immediately after each failure.

| Next action after a failure | Count |
|---|---:|
| retry `from_state` | 416 |
| different input, same tool | 193 |
| switched tool | 106 |
| `force_restart` | 49 |
| abandoned (no further rocq call) | 14 |

Principled backtracking with `from_state` dominates, which is the behaviour the
API documentation recommends. There were 81 stuck runs of 3 or more consecutive
failures. The worst runs:

| Length | Session |
|---:|---|
| 10 | DSDP secrecy, PISMC variant |
| 8 | DSDP secrecy chain + entropy |
| 6 | DSDP secrecy chain + entropy (several runs) |
| 6 | DSDP IND-CPA shell-link / trace bridge |

## 9. Intended versus observed behaviour

| Documented behaviour | Observed |
|---|---|
| Import caching, sub-second `rocq_check` | Confirmed, median 0.024 s |
| `last_valid_state` recovery | Confirmed, most common post-failure action (416) |
| `force_restart` "rarely needed" | Not borne out, 80 uses, often after auto-restart timeouts |
| `rocq_verify` rejects custom axioms | Never exercised, 0 calls |
| `rocq_step_multi` non-destructive, max 20 | Consistent with the spray-and-keep pattern |

## 10. Cross-reference with prior lessons

| Prior lesson | Status | Evidence in this corpus |
|---|---|---|
| "No node at point" under coq-lsp >= 0.2.4 | Confirmed, dominant | 245 failures, all before the 2026-06-02 patch; `rocq_query` and `rocq_assumptions` 100% down |
| PET timeout on large files | Confirmed | 38 `rocq_start` timeouts; p90 latency 30.1 s |
| Verification ladder, check is cheap | Confirmed | `rocq_check` median 0.024 s vs compile 5.5 s |
| `rocq_check` sufficiency | Supported | 1300 checks vs 93 compiles |
| `rocq_start` needs `.vo`, silent fails | Partial | 18 `rocq_start` reference-not-found |
| rocqworker OOM, kill does not propagate | Not observable | Infrastructure event, no tool-result trace; 0 unmatched calls |
| Always Search before writing tactics | Tension, novel | `rocq_query` was 100% broken, so MCP Search was unavailable this window |

Novel points: `rocq_query` and `rocq_assumptions` were not merely flaky but totally
down for the window. The recorded guidance to "always Search before writing
tactics" was effectively un-followable through MCP while `rocq_query` was broken, a
genuine process gap. `rocq_verify` and `rocq_notations` have never entered the
workflow.

## 11. Recommendations

**Tool-side.**

1. Treat the "No node at point" patch (2026-06-02) as load-bearing. Pin the
   coq-lsp / pet version and add a one-line smoke test, a `rocq_query "Check nat."`,
   so a future upgrade cannot silently re-break the read-only tools.
2. Raise or stage the 30 s start timeout for large files, or split files above
   about 1000 lines, to remove the `rocq_start` cliff.

**Usage-side.**

1. Adopt `rocq_verify` at proof-close. It is the cheapest guard against custom
   axioms and statement drift, and it is currently unused.
2. Use `rocq_notations` when a notation-ambiguity error appears, instead of guessing.
3. Keep leaning on `rocq_check` and `rocq_step_multi` for exploration. The data
   shows this loop works.

**Process-side.** Re-run `parse.py` after each burst of work. Watch for
`force_restart` spikes and runs of 3 or more consecutive failures as early signals
of a stuck session.

## Reproducibility

All numbers derive from `parse.py` (read only) over the project's transcript
directory under `~/.claude/projects/`. It writes `metrics.tex` (consumed by the
PDF), `metrics.json`, and `samples.txt`, and self-checks its counts against grep
priors and a greater-than-90% subagent-share gate before emitting anything. This
markdown was written from `metrics.json`.
