# Blueprint coverage checker

`check_coverage.py` mechanically guarantees the blueprint documents every
declaration in scope, and that no `\rocq{}` ref dangles.

## Scope

The `.v` files listed in `make_blueprint.sh`'s `MODULES` array, the exact set
the blueprint claims to document. At this commit that is seventeen files, in
the order MODULES lists them:

- `dumas2017dual/dsdp/counting/dsdp_entropy.v`
- `dumas2017dual/dsdp/counting/dsdp_random_inputs.v`
- `dumas2017dual/entropy_fiber/entropy_fiber_zpq.v`
- `dumas2017dual/lib/extra_proba.v`
- `computational_security/negligible.v`
- `computational_security/indcpa_game.v`
- `computational_security/indcpa_scheme_sequence.v`
- `computational_security/epshop.v`
- `computational_security/epshop_sequence.v`
- `dumas2017dual/dsdp/hopping/dsdp_instance.v`
- `dumas2017dual/dsdp/hopping/dsdp_alice_hop_secrecy.v`
- `dumas2017dual/dsdp/hopping/dsdp_alice_trace_link.v`
- `dumas2017dual/dsdp/hopping/dsdp_alice_main.v`
- `dumas2017dual/dsdp/hopping/dsdp_alice_instances.v`
- `computational_security/idealized_indcpa_scheme.v`
- `computational_security/paillier_indcpa_scheme.v`
- `computational_security/benaloh_indcpa_scheme.v`

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

At this commit the checker exits 0: `code=479 blueprint=239 excl=240`, no
UNCOVERED declaration and no DANGLING ref. Every declaration in scope either
has a `\rocq{}` node or an entry in `blueprint-exclude.txt`, so the next
declaration added, renamed or deleted breaks the check.

The scheme-sequence and sampling refactor added the nodes
`def:dsdp_enc_coins`, `def:interpreter_sample`, `lem:raw_trace_priv_keys`,
`lem:negligible_fun_inv_exp2`, `def:keygen_sequence`,
`def:indcpa_scheme_sequence`, `def:mk_dsdp_instance_sequence`,
`def:idealized_scheme_sequence`, `def:paillier_scheme_sequence` and
`def:benaloh_scheme_sequence`. Six declarations left the exclude-list for a
node of their own: the coin record with its cardinality and its uniform law,
Alice's corrupted-Alice data record, Charlie's re-encryption slot, the seed
streams a run is given, and the two private-key declarations of the executed
trace. `def:interpreter_sample` also cites `smc/smc_interpreter.v`, which is
outside `MODULES`, so the checker ignores those two refs and coqdoc builds no
page for them, as already happens for the `residuosity_game`,
`dsdp_relay_secrecy` and `dsdp_malicious_dotp` refs.

The per-instance scheme bounds are stated once, in
`dsdp_alice_instances.v`. `Section paillier` carries the instance and the instance
sequence, `paillier_assumption_dcrE` and `paillier_epsilon_dcrE`,
`paillier_trace_guess_V2_admissible_le` and `_admissible_pq_le` at the
section's own k, and `paillier_trace_guess_V2_negligible`; `Section benaloh`
carries the Benaloh counterparts, `benaloh_assumption_residuosityE` and
`benaloh_epsilon_residuosityE`, its `_admissible_pq_le` taking the block
size as a product of two numbers; `Section idealized` carries the witness
sequence and `alice_trace_guess_V2_idealized_negligible`. The nodes
`cor:alice_guess_paillier`, `cor:alice_guess_benaloh`, `def:idealized_setting`,
`def:paillier_setting`, `def:benaloh_setting`, `cor:paillier_security`,
`cor:benaloh_security` and `cor:idealized_security` point at them. The
scheme-sequence records those three sections read their instances off carry
nodes of their own in `computational_security/`, one per scheme, and each of
them cites the two negligibility lemmas the record derives rather than
assumes.

## Pre-commit hook (optional, opt-in)

`git-hooks/pre-commit-blueprint-coverage` is a standalone step, independent of
the rocq-audit hook. It runs only when a coverage-relevant file is staged, and
honors `BLUEPRINT_COVERAGE_BYPASS=1`. This repo's live `pre-commit` is a shared
symlink to the rocq-audit pipeline, so wiring is left as an explicit opt-in —
e.g. have the active `pre-commit` also run:

```
"$(git rev-parse --show-toplevel)/dumas2017dual/blueprint/git-hooks/pre-commit-blueprint-coverage"
```
