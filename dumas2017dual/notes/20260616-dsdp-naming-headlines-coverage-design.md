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
| `dsdp_alice_view_advantage_le` | `dsdp_problem_secure` | generic base-game IND-CPA `AdvantageE ≤ 2·ε_cpa`, any adversary |

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

### Relocation strategy (refactor-then-move)

Per theorem, primary method then fallback:

1. **Whole conclusion-section move** (lowest risk) — when a section contains
   only headline theorems plus their tightly-coupled `_alt`/helper lemmas and is
   parameterized by already-proven results as hypotheses, move the entire
   section to the apex. Applies to `Section bob_security`, `Section
   charlie_security`.
2. **Section-split then move** — when a headline sits at the end of a machinery
   section, split the section just before the conclusion so the machinery closes
   first (auto-exporting its lemmas), then move the trailing conclusion section
   to the apex and `Require` the machinery. Keeps the moved body close to
   verbatim. Applies to `US_compromised_leaks_V2`, `dsdp_centropy_uniform(_n)`,
   `relay_privacy_n`, `US_n_compromised_leaks_V1`, and the four
   guessing-triangle/entropy theorems in the fiber.
3. **Flagged fallback** — if a body cannot move without re-declaring an
   unwieldy section context (very deep entropy machinery), flag it to the user
   before falling back to a thin apex corollary (`exact: <theorem with args>`)
   for that one theorem. Default remains physical relocation.

Supporting files retain every machinery definition and lemma; only the headline
statements (and any `_alt` helper that travels with a whole-section move) leave.

## C. Blueprint coverage checker (Issue 5) — Phase C

`dumas2017dual/blueprint/check_coverage.py` — strict 1:1 with an exclude-list.

- **Scope** = the `.v` files whose modules appear in `make_blueprint.sh`'s
  MODULES array (the exact set the blueprint documents); single source of truth.
- **Declared set** = identifiers introduced by `Theorem | Lemma | Corollary |
  Fact | Remark | Example | Definition | Record | Inductive | Instance |
  Hypothesis | Variable | Axiom | Parameter` in those files, minus
  `blueprint/blueprint-exclude.txt`.
- **Blueprint set** = trailing identifiers of `\rocq{…}` refs in
  `blueprint/src/*.tex`.
- **Hard-fail** on: declared-but-uncovered (and not excluded), or
  blueprint-but-undeclared (dangling). Print `code=N blueprint=M excl=K`.
- **Wiring**: `make dsdp-blueprint-coverage` target plus a standalone fast
  pre-commit step, independent of the rocq-audit hook, with a
  `BLUEPRINT_COVERAGE_BYPASS=1` escape hatch.

The exclude-list seeds with genuine internal helpers; Phase C closes the gap by
adding `\rocq{}` nodes for headline-adjacent declarations and excluding the rest
until the checker passes.

## D. Sequencing — each phase build-green + own commit

1. **Phase R** — the five renames (mechanical). `make dsdp` green.
2. **Phase M** — create `dsdp_main.v`; whole-section moves (`bob_security`,
   `charlie_security`) + the trivial `dsdp_alice_view_advantage_le`. Green.
3. **Phase X** — section-split + move the embedded headlines (`US_*`,
   `dsdp_centropy_uniform(_n)`, the guessing triangle, entropy form,
   `relay_privacy_n`). Green.
4. **Phase C** — coverage script + exclude-list + make target + hook; populate
   nodes / exclude-list until green.

Rejected alternatives: relocate-first (forces two rounds of ref updates);
big-bang (un-bisectable).

## Risks

- **Deep-machinery entropy relocation** (`dsdp_centropy_uniform_n`) is the
  highest-effort move; covered by the Phase-X section-split method, with the
  flagged thin-corollary fallback if the body becomes unwieldy.
- **Blueprint module-name coupling**: coqdoc names HTML by full logical module
  name, so every rename and every relocation changes `\rocq{}` targets. The
  coverage checker (Phase C) is itself the guard that catches any missed ref.
- **Pre-commit hook interaction**: the coverage check is a separate fast script,
  not routed through the rocq-audit path that previously hung on `.v` renames.
- Nothing external to `dsdp/` imports these modules (they are top-of-chain), so
  renames are contained to the DSDP subtree, blueprint, and `_CoqProject`.
