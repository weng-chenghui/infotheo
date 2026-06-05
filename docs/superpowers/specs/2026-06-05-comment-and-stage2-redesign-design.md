# Comment contract and Stage-2 architecture redesign

Date: 2026-06-05
Status: design approved, pending written-spec review
Scope: `.claude/audit/` rule catalog and pipeline scripts

## Problem

The Rocq style-audit pipeline's comment rules feel too strict and burn Stage-2
tokens. Two rounds of grounded investigation and adversarial co-design refined
the problem and turned up a correctness bug:

1. The comment quality grade (H001 error, H002 four-part warning) is enforced by
   the Stage-2 LLM. Its `WHAT`/paraphrase requirement pushes authors to restate
   the statement in prose, which is the self-duplication the user objected to.
2. The headline "remove comment grading to save tokens" is mostly false. Stage 2
   chunks all `N` entities and makes one agent call per chunk regardless of which
   rules are active, so removing two rule stanzas saves marginal input tokens and
   zero agent calls.
3. D001 (unused hypothesis) is **unsound** as specified. A real lemma,
   `pgg-smc/groups/free_group_ball.v:59` `letter_inv_lt`, uses its section
   hypothesis `Hr : 0 < r` implicitly through a terminal `by`/assumption, so the
   name `Hr` never appears in the body. The string proxy and the current Tier-K
   LLM verifier (`bin/tier-k-verify.py:43-53`, which re-reads tactic text for the
   name) both false-positive it. This is most MathComp-idiomatic proofs.
4. Over 965 historical findings, `C001` and `E001` have never fired, `D001` is 21
   and unsound, and the real LLM consumer is `G001` (suffix-role naming) at 181.

So the genuine levers are not "when does Stage 2 run" but: move comment checks to
deterministic regex, move the kernel-decidable rules to a deterministic prover
pass with no LLM, retire the rules that never fire, and scope the surviving LLM
work to changed entities only.

## Goals

- Keep every declaration commented, with no self-duplication of the statement.
- Capture three intents: definition INTENT, helper COMPOSITION into main lemmas,
  and what MAIN lemmas mean for the project's purpose.
- Make comment checking deterministic and cacheable, off the LLM.
- Fix the D001 soundness bug with a kernel check.
- Cut real Stage-2 token cost by removing the kernel rules and the Tier-K second
  call from the LLM budget, scoping the surviving LLM to changed entities, and
  pruning the per-chunk prompt.

## Non-goals

- No change to the I-series naming rules, the S996 budget sentinel definition, or
  the report-merge exit-code contract (errors block, warnings do not).
- No claim that comment tagging alone saves tokens. The token win comes from
  Part B.

---

# Part A: comment tag contract

## Mechanism

Replace the agent-graded free-prose comment grade with structured TAGS validated
by Stage-1 regex plus a bounded `git grep`. The H-series leaves Stage 2 entirely
and becomes `stage1_only`.

## The contract

Every in-scope entity carries exactly one role tag inside its immediately
preceding `(** ... *)` block. Free prose may surround the tag; the tag is the
machine-checked part.

| Entity kind | Required tag | Captures |
|---|---|---|
| Definition / Fixpoint, non-`Local`, multi-line (per `h_series_applies`) | `@intent: <text>` | why the definition exists, what it models |
| Helper lemma | `@composes: <id>[, <id>...]` | downstream lemma(s) it feeds, helper or main |
| Main lemma: Lemma / Theorem / Fact / Corollary / Proposition | `@main <label>: <text>` | which project pillar it serves |

Every Lemma-family entity must carry either `@main` or `@composes`. That forces
each lemma to declare itself headline-or-helper.

`<label>` is drawn from a configurable list `main_purpose_labels` in
`config.yaml`, seeded:

```yaml
main_purpose_labels:
  - security      # hiding / leakage / indistinguishability, incl. asymptotic security from a gap
  - correctness   # the protocol recovers the right value
  - architecture  # interface, framework coupling, instance bridge, design
  - bound         # quantitative rate / gap / mixing / genus tradeoff
```

A lemma serving two pillars may list two, for example `@main security,correctness:`.

## Grammar (regex-decidable)

Inside the preceding comment block, after `(*`/`(**` and whitespace stripping:

- `@intent:` then non-empty text passing the content floor below.
- `@composes:` then one or more Rocq identifiers `[A-Za-z_][A-Za-z0-9_']*`,
  comma or space separated.
- `@main <label>:` then non-empty text passing the content floor, `<label>` (or
  each of a comma list) in `main_purpose_labels`.

Worked examples drawn from the repo:

```
(** word_collapse_security.  @main security: abelian words leak no card identity. *)
(** wreath_SecurityAsymptotic.  @main bound: Schreier-walk gap 17/20 bounds mixing. *)
(** wreath_rayleigh_Qsq_R.  @composes: wreath_SecurityAsymptotic *)
(** deck_perm.  @intent: canonical shuffle action on the deck index type. *)
```

No `WHAT`/paraphrase requirement survives. The tag names role and intent, never
the statement, which is the self-duplication fix.

## Content floor (anti-gaming and degeneracy)

A single regex metric, reused from the existing `H001.yaml:18-27` logic, defines
both the tag-value floor and the "substantive legacy comment" test. After
stripping `(*` `(**` `*)` and whitespace, content passes when ALL hold:

- at least 10 informative characters,
- at least 2 alphabetic tokens of length 3 or more,
- not solely `TODO` / `FIXME` / `WIP` / `XXX` / `???`,
- not equal to the entity identifier.

A tag value failing this floor counts as empty (`@main security: x` does not pass).

## `@composes` resolution

A bounded `git grep` for an exact declaration of the named target, requiring a
declaration keyword anchor in comment-stripped staged content:

```
git grep -nE '^\s*(Lemma|Theorem|Fact|Corollary|Proposition|Definition|Fixpoint)\s+<name>\b'
```

Comment stripping (reuse `strip_line_comments`, `stage1-regex.py:48`) before
resolving prevents `Used by:` comment-hit false positives; the keyword anchor and
`\b` prevent the `wreath_gap_R` vs `wreath_gap_R_le1` substring false positive. A
target with no matching declaration anywhere in the repo is a dangling reference.

## Severity

| Finding | Condition | Severity |
|---|---|---|
| H001 no-comment | in-scope entity, no role tag, no preceding comment present | error |
| H001 absent | in-scope entity, no role tag, preceding comment present, AND `touched_header` true | error |
| H001 degenerate | in-scope entity, no role tag, preceding comment present, `touched_header` false, comment fails the content floor | error |
| H001 grandfathered | in-scope entity, no role tag, preceding comment present, `touched_header` false, comment passes the content floor | warning |
| H002 empty | tag present, value fails the content floor | error |
| H002 bad-label | `@main <label>`, a label not in `main_purpose_labels` | error |
| H002 dangling | `@composes` target has no declaration in the repo | error |
| H002 malformed | unrecognized `@keyword`, missing colon, or tag wrong for the entity kind | error |
| H003 composes-not-main | `@composes` chain does not reach a `@main` node within the commit's entity graph | warning |
| H004 prose-pillar mismatch | agent judges prose inconsistent with the claimed pillar | warning, opt-in `comment_semantic_check`, default OFF |

Principle: any mechanically decidable broken contract is an error. The only
routine warnings are the migration nudge (H001 grandfathered), H003 reachability,
and the opt-in H004.

## Migration

`strict_comment_coverage` stays `false`, so the H-series is diff-scoped. The
manifest cannot distinguish a brand-new lemma from a signature edit, and does not
need to. The trigger redefines "new declaration" as `touched_header`:

- `touched_header` true: the declaration line changed (new lemma or signature
  edit). Require a tag, error if missing.
- `touched_header` false, body-only change, preceding comment present and passes
  the content floor, no tag: grandfather to warning.
- `touched_header` false, preceding comment present but fails the content floor,
  no tag: error (degenerate, treated as uncommented).
- No preceding comment present: error.

Implementation note: `tier0-extract.py` intersects an entity's `touched_lines`
with `[decl_line, end]`, so a comment-only edit above the declaration lands in
`unanchored_hunks`, never in the entity, and does not by itself bring the entity
into scope. A "comment edited" trigger is therefore both unimplementable from the
entity record and moot (a comment-only edit surfaces no entity). The migration
keys on `touched_header` and legacy-comment substance only.

The 36 in-flight files are not re-flagged en masse; they convert opportunistically.

## Scope

`h_series_applies` (`stage1-regex.py:118-139`) is unchanged: Lemma-family always
in scope; Definition/Fixpoint only when non-`Local`, multi-line, and the RHS is
not a single token. A single-line or `Local` Definition is out of scope and
carries no `@intent` requirement, which is the intended behavior. `Let` is not
emitted as a commit-time entity by `tier0-extract.py:100`, so `Let`-bound lemmas
are out of the contract; the divergence with `file_manifest.py:34` (file mode
emits `Let`) is documented and `Let` is excluded from the contract in both modes.

## Catalog and pipeline changes

- `H001.yaml`/`.md`: `stage_mode: both` to `stage1_only`. Rework the `fast_check`
  to the tag-absence and content-floor logic.
- `H002.yaml`/`.md`: `stage_mode: stage2_only` to `stage1_only`. Tag-validity
  logic (empty, bad-label, dangling, malformed), all error.
- New `H003`: `stage1_only`, warning, intra-manifest `@composes` reachability
  graph. Cross-file chains are disclosed as unverifiable, not flagged.
- New `H004`: `stage2_only`, warning, disabled by default behind
  `comment_semantic_check`.
- `AUTHORITY.md`: replace the four-part comment-template section with the tag
  contract.
- `config.yaml`: add `main_purpose_labels` and `comment_semantic_check: false`.
- `CLAUDE.md`: rewrite the "Comment quality (H-series)" section.
- Fixtures: rewrite `good`/`bad` for H001/H002, add for H003/H004. Remove the
  H001/H002 Stage-2 snapshot assertions, since both are now Stage-1.

---

# Part B: Stage-2 architecture

## Stage 1.5 deterministic kernel pass

A new script (for example `bin/stage1_5-kernel.py`) emits D001 and E001 with no
LLM. It runs at commit on the touched files' staged content.

Staged-blob materialization: write `git show :<file>` to a same-directory hidden
temp file (for example `pgg-smc/groups/.audit-<sha>.v`) and open it directly via
a single coq-lsp/rocq session, single process, no `-jN`. A `/tmp` copy is
rejected by the MCP workspace guard. The temp file is opened, never `Require`d,
so its own logical name never clashes; imports resolve through their `-R` mapping
and in-tree `.vo`.

D001, unused hypothesis, commit mechanism (clear-replay):
- emit only when `clear H` succeeds AND the proof replays verbatim,
- on `clear H` failure with a dependency error (H used in a later in-section
  type), abstain,
- on replay break after a successful clear, H is implicitly used, no finding.

D001 pre-merge cross-check (discharge-signature): after `End <Section>`,
`About <lemma>` shows whether the hypothesis statement survived the generalized
`forall`. Used as the authoritative `--full` pass.

E001, goal-closed-early: step the proof script minus its trailing terminator and
read the `proof_finished` boolean from `rocq_check`. Emit when true.

Abstain rule: on any open failure, stale import, parse error, or timeout, emit
nothing for that file and defer to the pre-merge `--full` run. Wall-clock gated
like Stage 2. Latency budget is per touched file, roughly 5s for the first lemma
in a file and milliseconds per later lemma or step, about 1.1GB RSS for one
session.

Soundness of abstain: D001 and E001 are warnings, and every blocking rule is
regex, so abstaining can only delay a warning to pre-merge, never drop an error
or raise a false block.

## Delete Tier-K

`bin/tier-k-verify.py` and its invocation are removed, along with the
`kernel_contract` routing in the pipeline. The kernel discovers D001/E001
directly and is self-verifying, so the second headless LLM call per finding no
longer exists.

## Retire C001

C001 has zero historical fires and its offending shape occurs zero times across
all Inductive/Record declarations in `pgg-smc`. Replace it with a cheap Stage-1
regex stub over `^\s*(Inductive|Record)\b[^.]*:\s*forall\s*\{` (currently zero
matches, zero cost) for future-proofing, off the LLM.

## Scope the commit-path LLM

After C001 to regex, D001/E001 to kernel, and the H-series to regex, the only
commit-time LLM work is G001, suffix-role naming, scoped to fire only on entities
whose declaration line changed (`touched_header`). It runs as a pruned
micro-call on at most `k` changed entities.

The pre-merge `--full` run keeps the full LLM surface: G001 over all entities,
the obfuscated A-series tail, the C001 edge, and H004 when enabled. A commit with
the LLM scoped this way can miss only a regex-evading `f_equal`/`pose proof` or a
novel C001 shape, both warnings, both caught at pre-merge.

## Per-chunk prompt pruning

`build_prompt` (`stage2-agent.py:145-171`) currently re-sends the full rule
catalog and full AUTHORITY.md per chunk. Prune to only the active rules' YAML and
Markdown plus the AUTHORITY sections those rules cite. For the commit-time
G001 micro-call that is the G001 stanza plus the `Standard suffixes` and
`Lemma naming grammar` sections, roughly 4k tokens.

## Locality chunking

Chunk changed entities by file and Section adjacency at `chunk_size = 3` so a warm
commit reuses the content-addressed cache maximally. Big flat chunks cut cold call
count but bust more cache on the common small commit; small locality chunks do the
opposite.

## Two run modes

- Commit gate: Stage-1 regex (errors block), Stage 1.5 kernel (D001/E001,
  abstain-on-failure), G001 header-scoped pruned micro-call.
- Pre-merge `--full`: adds the full LLM surface and the discharge-signature D001
  cross-check.

---

## Commit-gate soundness

The commit gate blocks only on error-severity findings, all of which come from
deterministic Stage-1 regex (I001, H001/H002 tag errors, A001/A002 literal) or
the Stage 1.5 kernel pass. The kernel pass is sound by construction: D001 emits
only when `clear H` succeeds and the proof replays verbatim, a kernel-checked
proof that H is unused; every other outcome yields no finding. E001 emits only
when the script minus its trailing terminator leaves `proof_finished` true. On
any failure the pass abstains, and since every kernel-emitted finding is a
warning, abstaining can only delay a warning. The LLM is absent from the blocking
path, so no nondeterministic judgment can block a commit.

## Token model

Assume about 45k tokens per chunk today, full catalog re-sent, `chunk_size = 3`.

| Scenario | Today | Final design |
|---|---|---|
| k=3, N=200, warm cache | the 1-3 chunks holding changed entities re-run at about 45k each, about 45-135k, plus a Tier-K LLM sub-call per D001/E001 | kernel D001/E001 = 0 LLM, plus about f times 5s wall; commit LLM is one pruned G001 micro-call on at most 3 entities, about 0-4k |
| k=N=200, cold | about 67 chunks times 45k, about 3.0M, trips the 2M daily cap and emits S996, blocks | kernel pass = 0 LLM; pre-merge `--full` on the pruned catalog about 0.6-0.9M, under cap; commit itself about 0 LLM |

## Residual risks and verification tasks

These are flagged as not-yet-proven and must be verified during implementation,
not assumed:

1. E001 kernel mechanism was reasoned but not run end-to-end in design. Validate
   the "drop trailing terminator, confirm `proof_finished` flips" mechanism on a
   real multi-subgoal proof before shipping E001.
2. H002 full regex-ability is asserted by analogy to H001. Confirm each tag-
   validity sub-check is regex-expressible.
3. Module-name clash on the pre-merge consumer-replay path is unverified. The
   same-directory hidden unique filename mitigates it; confirm no `Require` ever
   names the probe copy.
4. The `.vo` location assumption is in-tree (Makefile flow). A future switch to
   `dune` moving `.vo` into `_build/` changes import resolution for the staged
   blob and must be re-probed.
5. Latency numbers are single warm-cache samples; budget Stage 1.5 by touched-file
   count and gate it on wall-clock like Stage 2.

## Phasing

Phase 1, Part A: the comment tag contract. Self-contained, relieves the comment
strictness immediately. Lands and is verified first.

Phase 2, Part B: the Stage-2 architecture. Kernel Stage 1.5, delete Tier-K,
retire C001, scope the commit LLM to header-scoped G001, prune prompts, locality
chunking. Lands and is verified after Phase 1.
