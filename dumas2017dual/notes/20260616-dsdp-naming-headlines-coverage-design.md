# DSDP naming, headline centralization, and blueprint coverage — design

Date: 2026-06-16
Status: design approved; ready for implementation plan
Scope: `dumas2017dual/dsdp/` (post-reorg bucket tree from 20260615)

## Motivation (the five issues)

After the 20260615 bucket reorg the directory is structurally clean but has
naming and centralization debt:

1. `dsdp_indcpa_security.v` vs `dsdp_security_indcpa_fiber.v` — the names do not
   say which is which. They are a 2-stage pipeline (advantage bound → guessing /
   IT-fiber composition), not redundant; only the names collide.
2. `dsdp_symbolic.v` vs `dsdp_game_symbolic.v` — same problem (symbolic
   execution → game derivation).
3. `counting/dsdp_security.v` — the generic name oversells a file that is in
   fact the information-theoretic party-privacy analysis; it also sits oddly
   under the `counting/` bucket.
4. Headline theorems are scattered across `counting/` and `indcpa_hopping/`.
   There is no single apex file presenting the central results with the other
   files as support.
5. Nothing mechanically guarantees the blueprint documents every declaration; a
   rename can silently leave a dangling `\rocq{}` ref or an uncovered lemma.

## Decisions

- **Relocation, not re-export.** Headline proof bodies physically move into a
  new apex file `dumas2017dual/dsdp/dsdp_main.v`; supporting files keep the
  machinery. (Refactor-then-move: helpers a moved body calls are exported from
  the supporting file first.)
- **Coverage checker is strict 1:1 + exclude-list**, run as a fast standalone
  pre-commit step.
- **Rename-first sequencing**, each phase build-green and committed on its own.

## A. File renames (Issues 1–3) — Phase R

Short-name `Require Import` resolves by basename suffix, so renames touch only:
`git mv`, `_CoqProject`, internal `Require Import` lines, `make_blueprint.sh`
MODULES, blueprint `\rocq{}` refs (full module-name change), stale `.vo`.

The `Require Import` update must be driven by a **repo-wide** scan, not just the
five renamed files. Known non-renamed importer: `symbolic_game/dsdp_game_gen_literal.v`
requires `dsdp_symbolic` and `dsdp_game_symbolic`. (Stray `rocq_mcp_cache_*.v` at
the repo root are MCP scratch — ignore.)

| Bucket | Old → New | Holds after relocation |
|---|---|---|
| `symbolic_game/` | `dsdp_symbolic.v` → `dsdp_symbolic_exec.v` | symbolic execution: `Symbolic_DSDP_Interface`, `palice_sym`, observed combines, hop ciphertexts |
| `symbolic_game/` | `dsdp_game_symbolic.v` → `dsdp_game_derivation.v` | `game_of_trace`, `obs_of_procs`, the `dsdp_indcpa_secrecy_problem` record, generic `dsdp_indcpa_secrecy` |
| `indcpa_hopping/` | `dsdp_indcpa_security.v` → `dsdp_indcpa_advantage.v` | `dsdp_problem` instance, hop lemmas, `dsdp_advantage_derived(_leak_S)` |
| `indcpa_hopping/` | `dsdp_security_indcpa_fiber.v` → `dsdp_guess_fiber.v` | guessing experiment + Infotheo `1/m` fiber + exported branch helpers |
| `counting/` | `dsdp_security.v` → `dsdp_view_independence.v` | `Bob/CharlieView` independence lemmas, `dotp2`, `relay_security_n`, `malicious_n` |

## B. Apex `dumas2017dual/dsdp/dsdp_main.v` (Issue 4) — Phases M, X

New apex at the dsdp root (above the buckets); requires every axis file. Logical
name `infotheo.dumas2017dual.dsdp.dsdp_main`.

### Headline set and name mapping

Corrupted-Alice guessing triangle — `real = ideal + advantage`, one family:

| New name | Was | Statement |
|---|---|---|
| `dsdp_alice_guess_ideal_le` | `guess_sdistr_success_le` | guess ≤ `1/m` at the all-zero/ideal endpoint (IT branch) |
| `dsdp_alice_guess_advantage_le` | `guess_advantage_le` | `AdvantageE(real, ideal) ≤ 2·ε_cpa` (composing computational branch) |
| `dsdp_alice_guess_real_le` | `dsdp_alice_secrecy_leak_S` | guess ≤ `1/m + 2·ε_cpa` at the real endpoint (S exposed) |
| `dsdp_alice_unpredictability_ge` | `Hunp_ge_bound_leak_S` | `H_unp ≥ log m − log(1 + 2·m·ε_cpa)` (entropy form) |
| `dsdp_alice_view_advantage_le` | `dsdp_problem_secure` | IND-CPA bound for the concrete `dsdp_problem` instance, over any adversary: `AdvantageE(real_game dsdp_problem, zero_game dsdp_problem) ≤ 2·ε_cpa` (an `Example`) |

The generic any-problem parent of this bound is `dsdp_indcpa_secrecy`
(`AdvantageE ≤ count_obs_hops(P)·ε_cpa`, in `dsdp_game_derivation.v`); it stays
there as support and is not relocated.

Information-theoretic party privacy (names kept unless noted):

| New name | Was | Statement |
|---|---|---|
| `dsdp_centropy_uniform` | kept | `H(V2,V3 \| V1,U1,U2,U3,S) = log m` |
| `US_compromised_leaks_V2` | kept | corrupted `U2,U3` constant ⇒ `H(V2 \| AliceView) ≠ H(p_V2)` |
| `bob_privacy_V1`, `bob_privacy_V3` | kept | `H(V_i \| BobView) = log m > 0` |
| `charlie_privacy_V1`, `charlie_privacy_V2` | kept | `H(V_i \| CharlieView) = log m > 0` |

n-party generalizations:

| New name | Was | Statement |
|---|---|---|
| `dsdp_centropy_uniform_n` | kept | `H(VarRV \| CondRV) = log(m^n_relay)` |
| `relay_privacy_n` | `relay_privacy_logm` | `H(Y \| View) = log m > 0` for a generic relay |
| `US_n_compromised_leaks_V1` | `ConstUS_n_discloses_V1` | constant `US` ⇒ `Dotp_n_rv US VS = (fun t => VS t ord0)` |

### Relocation strategy (full physical relocation)

Every headline's proof body moves into `dsdp_main.v`. Two mechanisms by how
entangled the body is with section-local machinery.

**(1) Whole conclusion-section move — clean, LOW/MED effort.** When a section
contains only headline theorems plus their tightly-coupled `_alt` helpers and is
parameterized by already-proven results as hypotheses, the entire section moves
to the apex verbatim; its helpers travel with it, no argument threading.

- `Section bob_security` — LOW. Self-contained, takes `BobView_indep_V1/V3`,
  `pV1/pV3_unif` as Hypotheses.
- `Section charlie_security` — MED. Its `Let`s `CharlieView_indep_V1/V2` call
  `CharlieView_indep_V*_proven` from the separate `Section
  charlie_security_independence`, so the apex must `Require` the renamed
  `dsdp_view_independence` (which still holds the `_proven` lemmas) and the load
  order must place it before `dsdp_main`.
- `dsdp_alice_view_advantage_le` (was `dsdp_problem_secure`, an `Example`) —
  trivial: a two-line body over `dsdp_indcpa_secrecy` + `dsdp_problem_hops`.

**(2) Lift-out + re-section + argument-thread — HIGH effort, all of the following.**
The conclusion theorems are interleaved with their machinery inside one flat (or
nested) section, with no usable internal split point. Mechanism: delete the
conclusion theorems from the support section (the remaining machinery still
compiles and, at `End`, auto-generalizes each lemma over exactly the section
variables it uses), then in the apex re-open a section with the same
variables/hypotheses and paste each conclusion body, passing explicit arguments
to every now-exported machinery lemma. The compiler drives the arg lists; expect
~13–19 threaded args per call.

- Fiber guessing triangle + entropy form (`dsdp_alice_guess_ideal_le`,
  `_advantage_le`, `_real_le`, `dsdp_alice_unpredictability_ge`) — one flat
  `Section dsdp_guess_distribution`; `guess_advantage_eq` and the
  `real_game`/`guess_reduction` `Let`s are interleaved between the conclusions.
  Preserve the internal DAG (`ideal,advantage → real → unpredictability`).
- `dsdp_centropy_uniform`, `dsdp_centropy_uniform_n` — mid-section in
  `dsdp_entropy.v`, deepest entropy machinery.
- `US_compromised_leaks_V2` — 2-deep (`dsdp_security ⊃
  malicious_adversary_case_analysis`); drags the sibling `Section dotp2`
  apparatus (`dotp2, US, VS, ConstUS, S_E, ConstUS_discloses_V2, neg_self_inde`)
  and the `E_enc_inde` hypothesis.
- `relay_privacy_n`, `US_n_compromised_leaks_V1` — in `Section relay_security_n`
  / `Section malicious_n`.

Supporting files retain every machinery definition and lemma (now exported); only
the headline statements and proof bodies (plus the `_alt` helpers that travel
with a whole-section move) leave. No theorem is left behind as a thin corollary.

## C. Blueprint coverage checker (Issue 5) — Phase C

`dumas2017dual/blueprint/check_coverage.py` — 1:1 with an exclude-list, run as a
**baseline ratchet** rather than a one-shot 300-node documentation sprint.

- **Scope** = the `.v` files whose modules appear in `make_blueprint.sh`'s
  MODULES array. This is the blueprint's own documented set and includes three
  files OUTSIDE `dsdp/` (`homomorphic_encryption/indcpa_ror.v`,
  `entropy_fiber/entropy_fiber_zpq.v`, `lib/extra_proba.v`); the checker governs
  those too. ~463 keyword-matching declarations live in scope today versus ~38
  real `\rocq{}` nodes.
- **Declared set** = identifiers introduced by `Theorem | Lemma | Corollary |
  Fact | Remark | Example | Definition | Record | Inductive | Instance |
  Axiom`, minus `blueprint/blueprint-exclude.txt`. Section parameters
  (`Variable | Hypothesis | Context | Let`) are auto-excluded — they are never
  blueprint nodes.
- **Blueprint set** = trailing identifiers of `\rocq{…}` refs in
  `blueprint/src/*.tex` that match `\rocq\{infotheo\.[A-Za-z0-9_.]+\}`. The
  three documentation placeholders (`\rocq{...}`, `\rocq{<full declaration
  name>}`, `\rocq{M.decl}`) are skipped, not treated as dangling.
- **Hard-fail** on: declared-but-uncovered (and not excluded), or
  blueprint-but-undeclared (dangling). Print `code=N blueprint=M excl=K`.
- **Wiring**: `make dsdp-blueprint-coverage` target plus a standalone fast
  pre-commit step, independent of the rocq-audit hook, with a
  `BLUEPRINT_COVERAGE_BYPASS=1` escape hatch.

Phase C seeds `blueprint-exclude.txt` with the **current uncovered baseline**
(the several hundred non-parameter declarations with no node today; ~38 nodes
exist against ~360 blueprint-eligible decls after auto-excluding parameters) so
the checker passes immediately.
Its standing value is anti-drift: from then on every new declaration forces a
conscious "add a `\rocq{}` node or add to the exclude-list" decision, and every
rename is caught the moment its `\rocq{}` target goes dangling. The headline
theorems get real nodes; the baseline shrinks over time as blueprint prose grows.

## D. Sequencing — each phase build-green + own commit

1. **Phase R** — the five renames (mechanical). `make dsdp` green.
2. **Phase M** — create `dsdp_main.v`; whole-section moves (`bob_security`,
   `charlie_security`) + the trivial `dsdp_alice_view_advantage_le`. Green.
3. **Phase X** — lift-out + re-section + argument-thread the embedded headlines
   (`US_compromised_leaks_V2`, `dsdp_centropy_uniform(_n)`, the four fiber
   guessing/entropy theorems, `relay_privacy_n`, `US_n_compromised_leaks_V1`).
   All HIGH effort; one commit per support-file source so a failure is bisectable.
   Green.
4. **Phase C** — coverage script + exclude-list + make target + hook; populate
   nodes / exclude-list until green.

Rejected alternatives: relocate-first (forces two rounds of ref updates);
big-bang (un-bisectable).

## Risks

- **Argument-threading churn (the dominant risk)**: all ~9 embedded headlines
  are HIGH-effort lift-outs (~13–19 explicit args per machinery-lemma call),
  not just `dsdp_centropy_uniform_n`. Each is compiler-driven and mechanical but
  brittle; delegate to the rocq-prover agent and verify each support-file's
  relocation independently before the next. No thin-corollary fallback — full
  physical relocation is the chosen approach.
- **`US_compromised_leaks_V2` drags `dotp2` + `E_enc_inde`**: lifting it
  requires re-declaring the `dsdp_security` outer context and the exported
  `dotp2` apparatus in the apex; comparable to the entropy moves in difficulty.
- **Blueprint module-name coupling**: coqdoc names HTML by full logical module
  name, so every rename and every relocation changes `\rocq{}` targets. The
  coverage checker (Phase C) is itself the guard that catches any missed ref.
- **Pre-commit hook interaction**: the coverage check is a separate fast script,
  not routed through the rocq-audit path that previously hung on `.v` renames.
- Nothing external to `dsdp/` imports these modules (they are top-of-chain), so
  renames are contained to the DSDP subtree, blueprint, and `_CoqProject`. The
  one within-`dsdp/` sibling importer (`dsdp_game_gen_literal.v`) is why the
  Require-update scan in Phase R runs repo-wide rather than over the five files.
