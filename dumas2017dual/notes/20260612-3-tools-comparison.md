# AI proving tech lesson: fast dev-copy + direct rocq:rocq beats agent/autoprove on slow files

Date: 2026-06-12

## Context

Target: `guess_cinde_V2` and its prerequisite `guess_triple_pr` in
`dumas2017dual/dsdp/dsdp_security_indcpa_fiber.v`. Both now closed and committed
in the admit-free file at `299146b`.

The fiber file is large: a full `coqc` runs ~35-38s, and an interactive
`rocq_start` MCP call times out against the 30s budget. That single fact
invalidated the two default proving routes.

## What did not work, and why

**`rocq-prover` subagent — couldn't get traction.**
- `rocq_start` on the real file times out, so no interactive session ever opens.
- Delegated runs spun without persisting. Proofs that passed in a lenient
  `rocq_check` session were rejected by the real file's strict
  `Set Default Goal Selector "!"` mode, so nothing landed. Budget burned, zero
  progress on disk.

**`/rocq:autoprove` — too long (~30 min), same wall.**
- Autonomous multi-cycle (up to 20 cycles / 120 min). On a file where every
  `rocq_start` times out and each verify is a 35s batch `coqc`, the loop just
  re-hits the same wall, without the human correction the proof actually needed.

## What worked: fast dev-copy + direct rocq:rocq

1. **Make the file fast to load.** Create a throwaway dev copy (`dev_cinde.v`)
   with all ~67 prior proofs replaced by `Admitted`. Load time drops ~38s -> ~5s,
   so `rocq_start` opens it interactively.
2. **Develop step-by-step on the dev copy** via `rocq_step_multi` / `rocq_check`.
   Wrap the new lemmas in `Set Default Goal Selector "1"` so multi-sentence
   `have`-style proofs are allowed during development.
3. **Verify** until `proof_finished: true`.
4. **Port verbatim** into the real file; confirm with one batch `coqc` plus
   `Print Assumptions`.

## The lesson (generalizable)

- When `rocq_start` times out, the bottleneck is file load time, not the proof.
  Fix the load time first; everything else follows.
- The dev-copy / mass-`Admitted` trick converts a slow file into an interactive
  one without touching the proof you care about.
- A proof that passes `rocq_check` in a lenient session is NOT done: it must
  survive the real file's goal-selector / option settings. Always port back and
  batch-verify with the project build.
- Autonomous loops are the wrong tool when each cycle is dominated by a slow
  verify and the real blocker is interactivity. Hands-on `rocq:rocq` on a fast
  copy beats both `rocq-prover` and `/rocq:autoprove` here.
- Decision rule: if interactive `rocq_start` on the target file times out,
  do NOT delegate or autoprove. Build a fast dev-copy and drive `rocq:rocq`
  directly, then port-and-batch-verify.

## Tool-improvement analysis

Framing for treating this as a tool-improvement case study, not just a
practitioner workaround.

### The manual workaround IS the missing feature spec

Each manual step the human did is a tool gap. Automating it removes the need
for the human to know the trick:

- Manual mass-`Admitted` dev copy  ->  tool should offer a "fast interactive
  mode" that auto-stubs sibling proofs in the target file (or its prefix),
  opens the stubbed image for editing, and discards the stub on port-back.
  This is the single highest-leverage feature: it is what unblocked everything.
- Manual `Set Default Goal Selector "1"` wrapper during dev  ->  the dev
  session should emulate the target file's real option header, not a default,
  so dev-time and verify-time agree (see correctness item below).
- Manual port-verbatim + batch `coqc` + `Print Assumptions`  ->  tool should
  auto-port the verified proof into the real file and re-verify under the real
  options, reporting axiom hygiene.

### Severity ranking of the defects

1. **CORRECTNESS (highest): the verification oracle disagreed with ground
   truth.** A proof passed `rocq_check` in a lenient session yet was rejected
   by the real file's `Set Default Goal Selector "!"`. A green check that does
   not mean "done" silently misleads the agent and the human. Fix: the dev
   session must inherit the target file's exact option environment (goal
   selector, every `Set`/`Unset`, imports, notations) or explicitly diff and
   warn. This is more important than any speed fix.
2. **NO FAIL-FAST PRECONDITION.** Neither `rocq-prover` nor `/rocq:autoprove`
   checked "is `rocq_start` even viable on this file?" before committing to a
   long loop. Encoding the decision rule (rocq_start times out -> fast-copy
   route) as a router precondition would have avoided the ~30-min dead loop.
3. **NO INCREMENTAL PERSISTENCE.** `rocq-prover` spun with nothing written to
   disk. Checkpointing partial proofs each cycle would make a wasted run still
   leave usable state.
4. **FIXED, OPAQUE TIMEOUT.** The 30s `rocq_start` budget is a hard wall with
   no configurability and no progress signal; large files are simply
   unreachable interactively.

### Signals/metrics to capture for before/after evaluation

Needed to benchmark any fix; numbers I currently have are approximate and
some are not logged at all (gaps flagged):

- Load time, full vs stubbed: ~38s vs ~5s (approximate, not precisely logged).
- Full `coqc` time: ~35-38s. File line count: not recorded here.
- `rocq_start` timeout: 30s. Is it configurable? Unknown — needs checking.
- Number of prior proofs stubbed in the dev copy: ~67.
- Wall-clock / token cost of each failed route: `/rocq:autoprove` ~30 min;
  `rocq-prover` cost not measured. Cycle counts not logged.
- Success metric for a fix: manual dev-copy step eliminated; zero
  lenient-session false positives; no multi-cycle dead loops on time-out files.

### Generalization boundary

Applies to any file whose load/compile time exceeds the MCP `rocq_start`
budget (large developments, heavy imports, expensive `Section` bodies). Does
not apply to small fast-loading files, where the default routes work.

### Reproducibility gaps (to turn this into a benchmark)

Record, none of which is captured yet: machine spec, opam switch, infotheo /
mathcomp / rocq versions, rocq-mcp version, the exact target file and its line
count, and the commit (`299146b`). Without these the 38s/5s/30s numbers are
not reproducible.
