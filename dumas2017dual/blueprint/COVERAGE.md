# Blueprint coverage checker

`check_coverage.py` mechanically guarantees the blueprint documents every
declaration in scope, and that no `\rocq{}` ref dangles.

## Scope

The `.v` files listed in `make_blueprint.sh`'s `MODULES` array — the exact set
the blueprint claims to document (includes three files outside `dsdp/`:
`indcpa_ror.v`, `entropy_fiber_zpq.v`, `extra_proba.v`).

## What it checks (hard-fail on either)

- **Uncovered**: a declared `Theorem/Lemma/Corollary/Definition/Fixpoint/Record/
  Inductive(+constructors)/Instance/Axiom/…` in a scoped module with no `\rocq{}`
  node and not in `blueprint-exclude.txt`. Section parameters
  (`Variable/Hypothesis/Context/Let`) are auto-excluded.
- **Dangling**: a `\rocq{infotheo.…}` ref into a scoped module at an identifier
  that module does not declare.

Prints `code=N blueprint=M excl=K`; exits non-zero on failure.

## Run it

```
make dsdp-blueprint-coverage      # or: python3 dumas2017dual/blueprint/check_coverage.py
```

## Baseline ratchet

`blueprint-exclude.txt` is seeded with the declarations that have no node today,
so the checker passes immediately. Its standing value is anti-drift: a new
declaration must get a `\rocq{}` node or be added to the exclude-list, and a
rename is caught the moment its `\rocq{}` target goes dangling. Shrink the
exclude-list as blueprint prose grows (delete an entry once it gets a real node).

## Pre-commit hook (optional, opt-in)

`git-hooks/pre-commit-blueprint-coverage` is a standalone step, independent of
the rocq-audit hook. It runs only when a coverage-relevant file is staged, and
honors `BLUEPRINT_COVERAGE_BYPASS=1`. This repo's live `pre-commit` is a shared
symlink to the rocq-audit pipeline, so wiring is left as an explicit opt-in —
e.g. have the active `pre-commit` also run:

```
"$(git rev-parse --show-toplevel)/dumas2017dual/blueprint/git-hooks/pre-commit-blueprint-coverage"
```
