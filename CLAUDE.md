# Infotheo Project Instructions

## Compilation Safety (CRITICAL)
Each `rocqworker` process uses 2-10+ GB RAM (MathComp imports are huge).
Concurrent compilations WILL crash the machine (24 GB RAM).

Rules:
1. **Always use `make -j1`** (not `-j4`) for single-file compilation — this limits to 1 rocqworker.

## Proof Writing Rules (CRITICAL)
- **NEVER use `rewrite !lemma`** (bang `!` modifier) with arithmetic lemmas like `addn1`, `addnA`, `subnK`, etc. The `!` causes exponential rewriting on nat terms and can consume 60+ GB RAM, crashing the machine. Use explicit rewrites instead (e.g., `rewrite addn1 addnA` not `rewrite !addn1 !addnA`).
- `rewrite !lemma` is only safe with lemmas that apply at most a bounded number of times (e.g., `!inE`, `!mem_filter`).
- **NEVER use `lia`** — it is NOT available in this project. Use MathComp nat lemmas.
- **NEVER use `move/eqP` on Prop equalities** from `ltngtP`, `eqVneq`, `leqP`. These already produce Prop `m = n`. Use directly with `subst`/`rewrite`.
- **`ring_scope` warning**: `dumas2017dual/dsdp/dsdp_progress.v` has `Local Open Scope ring_scope`. Use `%N` for nat operations in ranking functions and arithmetic goals.
- **Rewrite order**: When unfolding rank/pose functions, unfold BEFORE substituting extracted equalities. E.g., `rewrite /rank Hi0 -Hjeq /=` not `rewrite -Hjeq /rank`.
- **Use `Show`** to inspect goals, **`apply I`** for type mismatches. Never guess what a goal looks like.
- **Use `apply ` and `exact `** (space, not colon) for better error messages when debugging.

## Agent Permissions
Subagents inherit the parent session's permissions. Before launching long-running
subagents (e.g., `rocq-expert-prover`), verify:
1. `Edit` and `Write` are in `~/.claude/settings.json` allow list (user-level)
2. `Bash(make:*)`, `Bash(rm:*)`, `Bash(ps aux:*)` are in `.claude/settings.local.json` (project-level)
3. If an agent reports permission denials, do NOT resume it — fix permissions first, then launch a fresh agent (resumed agents keep the old permission state)

## Build System
- Single file: `make -j1 <path>.vo`
- Force recompile: `rm -f <path>.vo` first if needed
- Paths: `-R . infotheo -R pgg-smc/... pgg_smc`

## Launching rocq-prover (Best Practices)
When launching `rocq-prover`, the parent MUST include in the prompt:
1. **Pre-built `.vo` dependencies status** — confirm that all imports are already compiled so the agent doesn't waste time on dependency builds.
2. **Exact line range** of the target lemma(s) (e.g., "lines 2340-2380 in pgg_raag.v").
3. **Section context** — list all `Variable`s and `Hypothesis`es in scope for the target lemma.
4. **Budget statement** — e.g., "You have a budget of 60 turns. Use `rocq_check`/`rocq_step_multi` for all intermediate testing. Maximum 2 full-file compilations."
5. **Explicit rocq-mcp reminder** — "Use the 4-phase workflow: `rocq_start` → explore with `rocq_query` → build proof with `rocq_check`/`rocq_step_multi` → apply once to real file."

## rocq-audit pre-commit pipeline

Every `git commit` that stages `.v` files runs a two-stage style audit.
The gate blocks the commit on any error-severity finding.

### Stages

- **Stage 1 (regex, always)**: fast literal checks driven by `fast_pattern` fields in `.claude/audit/rules/*.yaml`.
- **Stage 2 (agent, always)**: the `rocq-auditor` subagent (sonnet, read-only) reads the full rule catalog plus `AUTHORITY.md` and returns closeness-to-target findings in JSON. Low-confidence findings are re-run under opus. Output is validated against `.claude/audit/schema/auditor-response.schema.json`.
- **Tier K (kernel grounding, when Stage 2 claims it)**: findings with `kernel_contract: unused_hypothesis` or `goal_closed_at_line` are verified via rocq-mcp before being reported.

### Triggers

- Claude Code hook: `~/.claude/hooks/rocq-precommit-gate.sh` matches `git commit` in `PreToolUse(Bash)` and dispatches to `.claude/audit/bin/audit.sh`.
- Native hook: `.git/hooks/pre-commit` is a symlink into `.claude/audit/git-hooks/pre-commit` installed by `.claude/audit/bin/install-hooks.sh`.

### Files

- Template (canonical): `.claude/audit/template/config.yaml`, `template/rules/<ID>.yaml` + `.md`, `template/schema/`, `template/rules/AUTHORITY.md`.
- Fixtures: `.claude/audit/fixtures/{good,bad}/<ID>.v` tested by `lint-rules.py`.
- Runs (per audit invocation): `.claude/audit/runs/<YYYYMMDDTHHMMSSZ>-<diff8>-<rand4>/` with `config.yaml`, `rules/`, `schema/`, `reports/latest.md`, `fix-plans/<sha>.md`, `state/`, `meta.json`. The `runs/LATEST` symlink points at the most recent.
- Central state (cross-run): `.claude/audit/central-state/bypass.log`, `findings-history.ndjson`, `token-usage.json`, `last-run-id`, `stage2-cache/`, `attempts/<state_key>`, `oscillation/<state_key>.log`.
- The canonical config at `template/config.yaml` is never edited during an audit. `ROCQ_AUDIT_FIX_FLOW=1` causes `audit.sh` to synthesise `on_agent_failure: advisory` into the run's copy at `cp` time only.
- Machine readers resolve the current run via `central-state/last-run-id` (canonical text pointer). `runs/LATEST` is a best-effort human-convenience symlink and may be stale; automated tooling must not depend on it. `last-run-id` is written after the symlink attempt, so a race-read always returns a valid id.
- When Stage 2 hits the daily token cap, per-commit token cap, or wall-clock cap, `stage2-agent.py` emits an error-severity `S996` sentinel so the merge exits 2 rather than silently passing on an empty findings list.

### Commands

- `/rocq-audit run` — run the full audit; equivalent to `.claude/audit/bin/audit.sh`.
- `/rocq-audit lint` — validate the catalog and fixture pairs.
- `/rocq-audit new-rule <ID>` — scaffold a new rule.
- `/rocq-audit history` — render the dashboard.
- `/rocq-fix-plan` — after rejection, produce a plan with per-fix justification.
- `/rocq-apply-fixes <sha>` — apply an approved plan, then retry commit.

### Single-file audit (outside the commit flow)

For ad-hoc rule checks outside the commit flow, use
`.claude/audit/bin/audit-file.sh --file <path> [--entity PAT,...] [--lines N-M] [--rule ID,...]`.
Stage 2 runs by default (same gate semantics); pass `--stage1-only` for
regex only. Selector typos exit 3, not 0. The command does not write
to run metadata, findings-history, or bypass log; only the Stage 2
token counter is updated.

### Bypass

`ROCQ_AUDIT_BYPASS=1 git commit -m "emergency"` passes in advisory mode and logs the event to `refs/notes/audit-bypass` and `.claude/audit/state/bypass.log`. The `--no-verify` flag is forbidden policy because the Claude hook still fires.

### Naming conformance (I-series)

I001 blocks commits at **error** severity when a `Lemma`, `Theorem`, `Fact`, `Corollary`, `Proposition`, `Definition`, `Fixpoint`, `CoFixpoint`, `Let`, `Hypothesis`, or `Variable` name carries redundant kind-suffixes (`_lemma`, `_proof`), generic drift tokens (`_works`, `_test`, `_tmp`, `_old`, `_new`, `_foo`, `_helper`), or five-plus underscore components without a canonical MathComp suffix. Nested `let x := ... in` bindings are audited too.

To keep a non-conforming name, add a `Naming:` line in the preceding comment (or an inline `(* Naming: ... *)` on the let line). See `.claude/audit/rules/AUTHORITY.md` for the template.

### Comment quality (H-series)

Every touched `Lemma`, `Theorem`, `Fact`, `Corollary`, `Proposition`, and
multi-line non-`Local` `Definition`/`Fixpoint` must carry exactly one role tag in
its preceding comment: `@intent:` for a definition, `@composes: <lemma>` for a
helper, or `@main <label>:` for a main lemma, where `<label>` is from the
configurable `main_purpose_labels` (`security`, `correctness`, `architecture`,
`bound`). The full grammar and content floor are in
`.claude/audit/rules/AUTHORITY.md`.

These are deterministic Stage-1 regex checks (no LLM):

- H001 (error) fires when an in-scope declaration has no role tag. The
  `touched_header`-based migration grandfathers a substantive legacy comment on a
  body-only change to a warning; an absent or degenerate comment stays an error.
- H002 (error) fires when a tag is empty or degenerate, uses a `@main` label not
  in `main_purpose_labels`, names a `@composes` target with no declaration in the
  repo (`git grep`-resolved), or is malformed or wrong for the declaration kind.
- H003 (warning) fires when a helper's `@composes` chain dead-ends within the
  commit without reaching a `@main` lemma.

`main_purpose_labels` and `comment_semantic_check` live in
`.claude/audit/config.yaml`.

### Authoring a new rule

1. Run `/rocq-audit new-rule <ID>` (ID matches `^[A-Z][0-9]{3}$`).
2. Fill in `fast_pattern` for Stage 1, `agent_prompt` for Stage 2, or both.
3. Write the bad and good fixtures so each demonstrates one discriminating feature.
4. Run `/rocq-audit lint` to validate.
5. Commit the rule plus fixtures.

### Regression testing pipeline or catalog changes

Run `.claude/audit/bin/lint-rules.sh --full` before shipping changes to
the rule catalog or to pipeline scripts (`stage1-regex.py`,
`stage2-agent.py`, `report-merge.py`, `audit.sh`, `audit-history.py`).
`--full` runs the usual fixture-parity lint and then invokes
`audit-e2e-test.sh`, which covers deterministic pipeline regressions
for Defects 2 and 3 plus the pipeline half of Defect 1. The harness
does NOT invoke the Stage 2 LLM or test the fix agent; those are
verified manually by one `/rocq-apply-fixes` trial.
