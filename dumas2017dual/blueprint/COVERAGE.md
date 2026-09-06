# Blueprint coverage checker

`check_coverage.py` mechanically guarantees the blueprint documents every
declaration in scope, and that no `\rocq{}` ref dangles.

## Scope

The `.v` files listed in `make_blueprint.sh`'s `MODULES` array, the exact set
the blueprint claims to document. At this commit that is twelve files, in the
order MODULES lists them:

- `dumas2017dual/dsdp/counting/dsdp_entropy.v`
- `dumas2017dual/entropy_fiber/entropy_fiber_zpq.v`
- `dumas2017dual/lib/extra_proba.v`
- `computational_security/negligible.v`
- `computational_security/indcpa_game.v`
- `computational_security/epshop.v`
- `computational_security/epshop_family.v`
- `dumas2017dual/dsdp/hopping/dsdp_instance.v`
- `dumas2017dual/dsdp/hopping/dsdp_alice_hop_secrecy.v`
- `dumas2017dual/dsdp/hopping/dsdp_alice_trace_link.v`
- `computational_security/paillier_indcpa_scheme.v`
- `computational_security/benaloh_indcpa_scheme.v`

`dumas2017dual/dsdp/hopping/dsdp_instance_sequence.v` and
`dumas2017dual/dsdp/counting/dsdp_random_inputs.v` are not in MODULES, so the
checker never scans them and reports nothing about their declarations. A
`\rocq{}` ref into either is ignored rather than resolved, so such a ref can
neither cover a declaration nor be reported dangling.

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

`blueprint-exclude.txt` names the declarations in a scoped module that are
deliberately left without a node. Its standing value is anti-drift. A new
declaration must get a `\rocq{}` node or be added to the exclude-list, and a
rename is caught the moment its `\rocq{}` target goes dangling. Shrink the
exclude-list as blueprint prose grows. Delete an entry once it gets a real
node.

At this commit the checker exits 1. It reports 40 UNCOVERED declarations
across the scoped modules and 0 DANGLING refs. The UNCOVERED list is known
debt, not a regression to fix before the next commit.

The per-instance scheme bounds are stated once, in
`dsdp_instance_sequence.v`: the fixed-instance sections hold
`paillier_trace_guess_V2_admissible_le`, `_admissible_pq_le` and
`paillier_epsilon_dcrE` with the Benaloh triple, and the sequence sections
hold `paillier_epsilon_at_dcrE`, `paillier_trace_guess_V2_negligible` and
their Benaloh counterparts. The nodes `cor:alice_guess_paillier`,
`cor:alice_guess_benaloh`, `cor:paillier_security` and `cor:benaloh_security`
point at them. That module is outside MODULES, so those refs are not counted
in `blueprint=M`.

## Pre-commit hook (optional, opt-in)

`git-hooks/pre-commit-blueprint-coverage` is a standalone step, independent of
the rocq-audit hook. It runs only when a coverage-relevant file is staged, and
honors `BLUEPRINT_COVERAGE_BYPASS=1`. This repo's live `pre-commit` is a shared
symlink to the rocq-audit pipeline, so wiring is left as an explicit opt-in —
e.g. have the active `pre-commit` also run:

```
"$(git rev-parse --show-toplevel)/dumas2017dual/blueprint/git-hooks/pre-commit-blueprint-coverage"
```
