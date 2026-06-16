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
   There is no single main-results file presenting the central results with the other
   files as support.
5. Nothing mechanically guarantees the blueprint documents every declaration; a
   rename can silently leave a dangling `\rocq{}` ref or an uncovered lemma.

## Decisions

- **Relocation, not re-export.** Headline proof bodies physically move into a
  new main-results file `dumas2017dual/dsdp/dsdp_main.v`; supporting files keep the
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

## B. Main results `dumas2017dual/dsdp/dsdp_main.v` (Issue 4) — Phases M, X

New main-results file at the dsdp root (above the buckets); requires every axis file. Logical
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

### Relocation strategy (headline theorems only; clone context, full bodies)

One uniform rule for every headline. Move **only the headline theorem** — its
statement and its **full original proof body** — into a matching section in
`dsdp_main.v`. Do **not** move supporting lemmas/definitions, and do **not**
leave a thin `Proof. exact: <lemma>. Qed.` wrapper. Specifically:

1. **Clone the section context.** In the main-results file, open a section that re-declares
   the same `Variable`s and `Hypothesis`es, plus the context `Let`
   abbreviations the statement/proof refers to (`V1`, `V2`, `BobView`,
   `AliceView`, `US`, `ConstUS`, `guess_sdistr_success_real`, `CondRV`/`VarRV`,
   …). Variables and hypotheses are cloned; lemmas are not.
2. **Copy the full proof body verbatim**, then fix only the references that now
   cross the file boundary: each supporting lemma/definition the body calls
   stays in its (renamed) support file and exports when its section closes, so
   the moved body invokes it with explicit arguments (compiler-driven; expect
   ~13–19 args on the deepest fiber/entropy calls).
3. **Leave every non-headline declaration in place** — best effort, no
   supporting lemma moves. Orphan-but-stays (a support lemma whose only
   remaining consumer is the main-results file) is acceptable; it is not promoted to the
   main-results file. The `bob_privacy_V1_alt`/`_V3_alt`, `charlie_privacy_*_alt`,
   `dsdp_problem`/`dsdp_problem_hops`, `dsdp_g`/`S_determined`, the whole fiber
   guessing scaffold, the outer `dsdp_security`/`dotp2` apparatus, the
   `dsdp_entropy_n` and `malicious_n` sections — all remain in their files.

Effort by headline (drives Phase-X commit granularity):

- **Trivial** — `dsdp_alice_view_advantage_le` (was `dsdp_problem_secure`):
  two-line body over `dsdp_indcpa_secrecy` + `dsdp_problem_hops` (both stay).
- **LOW/MED** — `bob_privacy_V1/V3`, `charlie_privacy_V1/V2`: short bodies that
  call their staying `_alt` helpers + a uniformity hypothesis; clone the bob /
  charlie `Let` context. Charlie additionally needs the main-results file to `Require`
  `dsdp_view_independence` (its `CharlieView_indep_V*_proven` stay there).
- **HIGH (arg-threaded full bodies)** — `US_compromised_leaks_V2`,
  `dsdp_centropy_uniform`, `dsdp_centropy_uniform_n`, the four fiber
  guessing/entropy theorems, `relay_privacy_n`, `US_n_compromised_leaks_V1`:
  clone the (sometimes nested) section context, paste the full body, thread
  explicit args to the staying machinery. Preserve the fiber internal DAG
  (`ideal, advantage → real → unpredictability`) among the four moved theorems.

After the move each support file keeps its machinery exported and compiling;
`dsdp_main.v` holds 14 headline theorems (+ the cloned contexts) with real proof
text, no redirections.

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

## D. Sequencing + branch isolation

The mechanical, low-risk work lands on the working branch `itp2026-dumas2017dual`;
the large theorem relocation is isolated on a separate branch that is committed
but **not merged back**.

**On `itp2026-dumas2017dual` (commit each, bypass the rocq audit hook):**

1. **Spec finalization** — this document at the final model.
2. **Phase R** — the five renames (mechanical, repo-wide Require scan incl.
   `dsdp_game_gen_literal.v`). `make dsdp` green.
3. **Phase C** — coverage script + exclude-list (seed the current uncovered
   baseline) + make target + standalone pre-commit step. Checker green.

**Then branch off `itp2026-dumas2017dual` for the main-file move (do not merge back):**

4. **Phase M** — create `dsdp_main.v`; clone contexts + copy full bodies for the
   trivial + LOW/MED headlines (`dsdp_alice_view_advantage_le`, `bob_privacy_*`,
   `charlie_privacy_*`). Green.
5. **Phase X** — clone contexts + copy full bodies (arg-threaded) for the HIGH
   headlines (`US_compromised_leaks_V2`, `dsdp_centropy_uniform(_n)`, the four
   fiber guessing/entropy theorems, `relay_privacy_n`, `US_n_compromised_leaks_V1`);
   one commit per support-file source so a failure is bisectable. Green. Commit
   on the branch, leave unmerged.

Rejected alternatives: relocate-first (forces two rounds of ref updates);
big-bang (un-bisectable); moving orphan machinery into the main-results file (balloons it into
the whole derivation and guts the support files).

## Risks

- **Argument-threading churn (the dominant risk)**: the HIGH headlines copy full
  bodies that call staying machinery with ~13–19 explicit args per call. The
  supporting lemmas are not moved, so the main-results file bodies cross the file boundary on
  every call. Compiler-driven and mechanical but brittle; delegate to the
  rocq-prover agent and verify each headline before the next. The full body is
  copied, never reduced to a `Proof. exact: <lemma>. Qed.` wrapper.
- **Context cloning fidelity**: the cloned `Variable`/`Hypothesis`/context-`Let`
  block in the main-results file must match the support section exactly (same names/types) or
  the staying lemmas will not unify when called. `US_compromised_leaks_V2` is the
  worst case — it needs the nested `dsdp_security` outer context plus the
  statement-level `dotp2`/`US`/`ConstUS`/`AliceView` `Let`s cloned, while
  `dotp2`, `ConstUS_discloses_V2`, `neg_self_inde`, `E_enc_inde` stay in support.
- **Blueprint module-name coupling**: coqdoc names HTML by full logical module
  name, so every rename and every relocation changes `\rocq{}` targets. The
  coverage checker (Phase C) is itself the guard that catches any missed ref.
- **Pre-commit hook interaction**: the coverage check is a separate fast script,
  not routed through the rocq-audit path that previously hung on `.v` renames.
- Nothing external to `dsdp/` imports these modules (they are top-of-chain), so
  renames are contained to the DSDP subtree, blueprint, and `_CoqProject`. The
  one within-`dsdp/` sibling importer (`dsdp_game_gen_literal.v`) is why the
  Require-update scan in Phase R runs repo-wide rather than over the five files.

## Addendum — unsound encryption-independence cluster removed (commit d3098a9)

The information-theoretic party-view privacy results rested on the unsound
idealization that AHE encryption hides perfectly: the `E_enc_inde` hypothesis,
its siblings `inde_Echarlie`/`inde_Ebob`, and the `BobView/CharlieView _|_ V_i`
antecedents only dischargeable through encryption-independence. The whole cluster
was deleted.

- **Headlines removed (main 14 → 9):** `US_compromised_leaks_V2`, `bob_privacy_V1`,
  `bob_privacy_V3`, `charlie_privacy_V1`, `charlie_privacy_V2`.
- **Support removed:** in `dsdp_view_independence.v` the Sections
  `dsdp_view_independence` (the `E_enc_inde` scaffold + `dotp2` +
  `malicious_adversary_case_analysis`), `bob_security(_independence)`,
  `charlie_security(_independence)` (1483 → 199 lines); in `dsdp_entropy.v` the
  Section `dsdp_privacy_analysis` (1168 → 725 lines).
- **Kept (sound, no encryption-independence assumption):** `dsdp_centropy_uniform(_n)`
  (plaintext solution-counting), `relay_privacy_n`, `US_n_compromised_leaks_V1`,
  the IND-CPA `dsdp_alice_view_advantage_le`, and the SSProve guessing triangle +
  `dsdp_alice_unpredictability_ge` (the `1/m` output-fiber bound).
- **Follow-up:** `dsdp_view_independence.v` now holds only `relay_security_n` +
  `malicious_n`; its filename no longer matches its contents (rename candidate).
