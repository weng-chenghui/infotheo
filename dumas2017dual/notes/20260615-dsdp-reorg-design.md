# DSDP file-tree reorganization — design spec

Date: 2026-06-15
Scope: `dumas2017dual/dsdp/` only. `dumas2017dual/lib/` and `dumas2017dual/entropy_fiber/` are out of scope and untouched.

## Goal

The `dsdp/` directory holds ~22 `.v` files at one flat level, mixing the live
formalization, a superseded hand-written security development (`ref/`), and
untracked dev clones/scratch/probe files. Reorganize into axis subdirectories so
each file's role is legible from its path, and relegate unused files to a
two-tier `legacy/`.

## Key technical enabler

The whole project compiles under a single recursive load-path mapping, `-R . infotheo`
(root `_CoqProject`). Every `.v` gets a logical name `infotheo.<physical-path>.<basename>`.
All DSDP files import each other by **short name** (`Require Import dsdp_program`),
which Coq resolves by **basename suffix** against the load path. Verified facts:

- All `dsdp_*` basenames are unique project-wide (`find ... -name 'dsdp_*.v' | basename | sort | uniq -d` is empty).
- Nothing in the in-build set outside `dsdp/` requires any `dsdp_*` file (only scratch/cache/audit files do, none in `_CoqProject`).

Consequence: **moving a file into a subdirectory does not break any `Require`**,
because the basename is unchanged and stays unique. Only two things must change
for a move: the file's path line in `_CoqProject`, and the regenerated `Makefile.coq`.
No `Require` line is edited in the move phases.

The build is driven by `coq_makefile`: root `Makefile` invokes it over `_CoqProject`
to produce `Makefile.coq`. So the build-side edit is: update paths in `_CoqProject`,
regenerate `Makefile.coq`. The `DSDP_VO` make variable is computed by grepping `_CoqProject`
(`^(smc/|homomorphic_encryption/|dumas2017dual/)`), so subdir paths flow through automatically
once `_CoqProject` is updated; `DSDP_DIRS := ... dumas2017dual` is cleaned recursively, so the
`make dsdp-rebuild` target covers the new subdirectories.

### Logical names change on move — the blueprint consumes them

The plan's enabler covers Coq `Require` resolution, but the logical name itself DOES change on
move (`infotheo.dumas2017dual.dsdp.dsdp_symbolic` becomes
`infotheo.dumas2017dual.dsdp.symbolic_game.dsdp_symbolic`). `coqdoc` names its HTML output by the
full logical module name, and the blueprint links to those names. So moving a file that the
blueprint cites breaks the blueprint unless the blueprint is updated in lockstep. Affected:

- `blueprint/make_blueprint.sh` `MODULES=(...)` array hard-codes flat paths for 6 moved modules:
  `dsdp_symbolic`, `dsdp_game_symbolic`, `dsdp_game_code`, `dsdp_indcpa_security`, `dsdp_entropy`,
  `dsdp_security_indcpa_fiber`.
- `blueprint/src/content.tex` and `blueprint/src/it_bound_bridge.tex` hold 102 `\rocq{...}`
  references using the full logical name of those modules
  (`dsdp_security_indcpa_fiber` 31, `dsdp_game_symbolic` 27, `dsdp_game_code` 22, `dsdp_symbolic` 10,
  `dsdp_indcpa_security` 9, `dsdp_entropy` 3).

These are updated in a dedicated phase (B2). This is the only place file content (non-`.v`) is edited.

## Target tree

Buckets below reflect the Phase-A scan (`20260615-dsdp-reorg-inventory.md`): `dsdp_security`
resolved to `counting/`, and `convert/` resolved to CREATE (extract the fiber file's generic
conversion block).

```
dsdp/
  core/            interface, session_types, program, pismc, correctness
  symbolic_game/   symbolic, game_code, game_symbolic, game_gen_literal
  indcpa_hopping/  indcpa_security, security_indcpa_fiber
  counting/        entropy, entropy_trace, security
  convert/         dsdp_convert (generic SDist<->fdist + Pr_code framing lemmas, extracted in D)
  legacy/
    scratch/       chlipala, dsdp_security_indcpa_clone, dsdp_security_indcpa_concrete_clone,
                   dsdp_security_indcpa_pismc_clone, probe_fiber_reflection,
                   scratch_fiber_dev, syntax, syntax_demo
    superseded/    ref/dsdp_security_indcpa, ref/dsdp_security_indcpa_concrete,
                   ref/dsdp_security_indcpa_pismc, ref/dsdp_trace_bridge
                   + README.md pointing to the live replacement
```

### Bucket rationale

- **core/** — protocol definition and embedding: types/interface, session types, the
  DSDP program, the piSMC embedding, and the correctness proof. `dsdp_correctness.v`
  is the live file that instantiates the concrete Benaloh/Paillier AHE schemes, so the
  concrete schemes remain exercised in the build after `ref/` leaves it.
- **symbolic_game/** — the symbolic walk that auto-derives the SSProve game: the symbolic
  trace (`dsdp_symbolic`), the generated game code (`dsdp_game_code`), the symbolic game
  (`dsdp_game_symbolic`), and the legible literal mid-point (`dsdp_game_gen_literal`).
- **indcpa_hopping/** — the IND-CPA game-hopping result: the generic secrecy theorem
  (`dsdp_indcpa_security`) and the final composed bound (`dsdp_security_indcpa_fiber`,
  `dsdp_alice_secrecy_leak_S <= 1/card_msg + 2*epsilon_cpa`).
- **counting/** — the information-theoretic / solution-counting leg: `dsdp_entropy` and
  `dsdp_entropy_trace`.
- **convert/** — CONDITIONAL. Holds an extracted SDist<->fdist conversion library only if
  the scan finds a cleanly-liftable conversion core shared across files. Otherwise this
  directory is not created and the conversion code stays where it is.

### Files whose bucket the scan adjudicates

- **`dsdp_security.v`** (1645 lines; requires `dsdp_program`, `dsdp_entropy`): live but
  ambiguous — could be `counting/`, `indcpa_hopping/`, or partly superseded. The
  per-declaration scan decides, with evidence, at the Phase-A checkpoint.
- **`convert/` existence and contents**: decided from the straddler list at the checkpoint.

### Legacy justification (evidence)

`ref/*` is a self-contained dead-end cluster: the only in-build consumers of any `ref/`
file are other `ref/` files; the live auto-derivation path
(`dsdp_symbolic -> dsdp_game_symbolic -> dsdp_indcpa_security -> dsdp_security_indcpa_fiber`)
imports none of them.

- `ref/dsdp_security_indcpa.v` (2507 lines, 0 `Admitted`) proves the same headline bound
  `Pr[...] <= 1/m + 2*epsilon_cpa` that the live `dsdp_security_indcpa_fiber.v` now
  produces by auto-derivation. Superseded.
- `ref/dsdp_security_indcpa_concrete.v` (1277 lines): the security-side Benaloh/Paillier
  concrete instantiation; its header records that the original chain was retired. The
  live build still exercises Benaloh/Paillier via `dsdp_correctness.v`.
- `ref/dsdp_security_indcpa_pismc.v` (782 lines): rests on an open `Hypothesis
  game_real_eq_pismc`.
- `ref/dsdp_trace_bridge.v` (356 lines): partial bridge that explicitly does not discharge
  that hypothesis.

The untracked clones/probe/scratch and the empty `dsdp_syntax.v` and the unused demo
`dsdp_syntax_demo.v` are throwaway dev artifacts -> `legacy/scratch/`.

## Legacy policy

`legacy/**` is dropped from `_CoqProject` entirely: nothing under `legacy/` compiles in the
build.

Move mechanics differ by git status (`git mv` fails on untracked files):

- **Tracked legacy files** -> `git mv` (history preserved): `dsdp_syntax.v`, `dsdp_syntax_demo.v`,
  and the four `ref/*` files.
- **Untracked legacy files** -> plain `mv` then `git add`: `dsdp_chlipala.v`,
  `dsdp_security_indcpa_clone.v`, `dsdp_security_indcpa_concrete_clone.v`,
  `dsdp_security_indcpa_pismc_clone.v`, `probe_fiber_reflection.v`, `scratch_fiber_dev.v`.

The pre-existing untracked dev scratch directory `dsdp/.scratch/` (5 probe/audit `.v` files, none
in `_CoqProject`) is OUT of scope: left untouched and untracked. Re-checks that scan `find dsdp
-name '*.v'` must exclude `.scratch/`.

## Scan and labelling method (Phase A)

1. **Declaration index (mechanical).** Parse the `.glob` files for every `Definition /
   Lemma / Theorem / Corollary / Record / Hypothesis / Variable / Instance / Notation` with
   its kind and source line. Exact symbol table, no guessing.
2. **Per-file labelling (parallel, read-only agents).** One `Explore` agent per in-scope
   file. Input: the file plus its declaration index. Output per declaration:
   `{name, kind, line, axis, one-line role, straddle?}`, where `straddle? = true` flags a
   declaration whose true axis differs from the file's primary bucket (these are the
   `convert/` extraction candidates).
3. **Inventory artifact.** Merge into `dumas2017dual/notes/20260615-dsdp-reorg-inventory.md`:
   a file -> bucket table plus the straddler list. This is the review checkpoint.

## Execution phases

Each phase is verified and committed before the next begins.

- **A — Scan.** Build index, run parallel labelling, write inventory memo, commit it.
  CHECKPOINT: review inventory; confirm `dsdp_security`'s bucket; decide whether `convert/`
  is extracted (and, if so, its exact contents).
- **B1 — Moves.** Create bucket dirs. `git mv` each live file into its bucket. Relocate legacy
  files by git status (see Legacy policy): `git mv` tracked, `mv` + `git add` untracked, into
  `legacy/scratch/`; `git mv` `ref/*` into `legacy/superseded/`. Update `_CoqProject` paths;
  remove all `legacy/**` lines from it. Regenerate `Makefile.coq`. Add `dsdp/README.md`
  (bucket map) and `legacy/superseded/README.md` (what replaced these). No `.v` content edits.
- **B2 — Blueprint sync.** Update the 6 moved-module paths in `blueprint/make_blueprint.sh`
  `MODULES`. In `blueprint/src/content.tex` and `blueprint/src/it_bound_bridge.tex`, rewrite
  every `infotheo.dumas2017dual.dsdp.<m>.` prefix to `infotheo.dumas2017dual.dsdp.<bucket>.<m>.`
  for the 6 moved modules:
  `dsdp_symbolic`, `dsdp_game_symbolic`, `dsdp_game_code` -> `symbolic_game`;
  `dsdp_indcpa_security`, `dsdp_security_indcpa_fiber` -> `indcpa_hopping`;
  `dsdp_entropy` -> `counting`. Order the rewrites longest-basename-first so
  `dsdp_security_indcpa_fiber` is not partially matched by a shorter prefix.
- **C — Verify.** `make dsdp-rebuild` (deletes stale `.vo/.vos/.vok/.glob` under DSDP_DIRS, then
  rebuilds DSDP_VO from the updated `_CoqProject`). Confirm a clean build. Re-run the blueprint
  build (or at least its coqdoc step over `MODULES`) to confirm B2. Re-check basename uniqueness.
  Commit.
- **D — `convert/` extraction** (only if approved at the Phase-A checkpoint). Extract the
  conversion core into `convert/dsdp_convert.v`, fix imports, re-prove, re-verify, commit.

## Verification strategy

The reorganization changes physical paths, not `.v` logic. The build is the verification: after
B1/B2, `make dsdp-rebuild` over the updated `_CoqProject` must succeed for all in-build `dsdp`
files, AND the blueprint build must succeed (its links resolve to the new logical names). A green
Coq build with unchanged `.v` contents plus a green blueprint build is sufficient evidence the
moves and the blueprint sync are sound. `make dsdp-rebuild` (not a plain rebuild) is used so stale
old-path `.vo/.glob` left behind by `git mv` are deleted first.

## Non-goals

- No `Require` line is edited for the moves (basename resolution handles it).
- `lib/` and `entropy_fiber/` are untouched.
- `dsdp/.scratch/` is untouched (out of scope, stays untracked).
- No `.v` content changes in any phase except D's extraction. The ONLY non-`.v` content edited is
  the blueprint (`make_blueprint.sh` + the two `.tex` sources) in B2, driven by the logical-name
  change, not by any logic change.
- No deletions: legacy is relocated, not removed (git history already preserves prior state).

## Risks and mitigations

- **Blueprint links break (BLOCKER found in audit).** Moving a cited file changes its logical
  name and orphans its coqdoc HTML. Mitigation: Phase B2 updates `make_blueprint.sh` `MODULES`
  and all 102 `\rocq{}` references; Phase C rebuilds the blueprint to confirm.
- **`git mv` on untracked files fails (BLOCKER found in audit).** Mitigation: per Legacy policy,
  only the 6 tracked legacy files use `git mv`; the 6 untracked use `mv` + `git add`.
- **Stale `.vo/.glob` after `git mv` mislead the scan or the build.** Mitigation: verify via
  `make dsdp-rebuild`, which deletes them before rebuilding.
- **Basename collision after a move** would make a short `Require` ambiguous. Mitigation:
  basenames verified unique project-wide; moves never rename; re-check after moves with
  `find dsdp -name '*.v' -not -path '*/.scratch/*' | xargs -n1 basename | sort | uniq -d`.
- **A `legacy/**` file silently needed by an in-build file.** Mitigation: verified no in-build
  file requires any `ref/*` or any untracked clone; the Phase-C build would fail loudly otherwise.
- **`Makefile.coq` not regenerated** would build stale paths. Mitigation: regenerate via the root
  `Makefile`'s `coq_makefile` invocation in B1 and confirm in C.
