# Statement-readability refactor — design spec (2026-07-29)

Approved scope: all stages, plus blueprint dependency-graph repair.
Branch: `20260729-0028-reduction-form-security` (continue in place).
Revision 2: adversarial audit of 2026-07-29 (verdict REWORK) applied — root
cause 1 rediagnosed (missing `Set Implicit Arguments`, new Stage 0), the
`Definition`/`Let` placement fixed against section boundaries, `eps`
parameterized over the adversary, `Section dsdp_alice_indcpa` added to
Stage 1, coverage-ratchet verification added, `\rocq`-link bullet dropped,
counts corrected.

## 1. Problem

Headline theorem statements in `dsdp/dsdp_main.v` are unreadable: the worst,
`dsdp_alice_guess_V2_real_le` (:794), spends 29 statement lines of which ~16
are two verbatim-repeated `indcpa_epsilon` application blocks, and its proof
re-spells the same subterms for 83% of its 29 lines. A five-agent scan
(2026-07-29) over the blueprint dependency chains of all 14 headlines (74
distinct blueprint nodes, 8 `.v` files) found the same disease at 22
high-severity and ~30 medium-severity statements, with a homogeneous cause.

## 2. Evidence base

### 2.1 High-severity targets (statement unreadable as-is)

| file | targets (line) |
|---|---|
| `dsdp/dsdp_main.v` | `dsdp_alice_view_advantage_le` :131, `dsdp_alice_guess_advantage_le` :749, `dsdp_alice_guess_V2_real_le` :794, `dsdp_alice_unpredictability_entropy_ge` :861, `dsdp_alice_simulation_advantage_le` :938 |
| `dsdp/indcpa_hopping/dsdp_indcpa_advantage.v` | `dsdp_derived_game_advantage_le` :69, `advantage_hop_leak_S` :272, `advantage_sum_ladder_le_leak_S` :318, `advantage_le_leak_S` :363, `dsdp_derived_game_advantage_le_leak_S` :443 |
| `dsdp/indcpa_hopping/dsdp_guess_fiber.v` | `gc_eq` :298 (553-char line), `guess_triple_proj_code` :690, `view_marginal_indep` :716, `guess_run_cells` :893, `guess_inner_kernel_form` :978 |
| `dsdp/symbolic_game/dsdp_game_code.v` | `advantage_sum_ladder_le` :928, `advantage_game_code_dsdp_le` :1075 |
| `dsdp/symbolic_game/dsdp_game_derivation.v` | `walk_obs_dsdp_leak_S` :310, `obs_of_procs_dsdp` :437, `obs_of_procs_dsdp_leak_S` :460, `dsdp_indcpa_secrecy_le` :698 |
| `dsdp/simulation/dsdp_simulator.v` | `dsdp_advantage_sim_le` :281 (14 of 16 lines identical with `dsdp_main.v`:957-972 — one statement pair, two spellings) |
| `dsdp/counting/dsdp_entropy.v` | `Pr_dsdp_sol_uniform` :237, `dsdp_centropy1_uniform` :262, `dsdp_centropy1_uniform_n` :679 (post-discharge arity 9–10 at call sites) |

### 2.2 Medium-severity targets (covered by the same abbreviations)

`dsdp_main.v`: `US_n_compromised_leaks_secret` :366, `dsdp_alice_guess_V2_zero_le`
:730. `dsdp_game_code.v`: `advantage_hop` :885, `advantage_le` :977,
`denote_game_shim_valid` :649. `dsdp_guess_fiber.v`: the `denote_run_caps`
family (9 statements: :479, :501, :526, :571, :577, :584, :590, :595,
:604), the `resolve (pack predictor) …` family (6 statements),
`guess_resolved_par` :362, `guess_inner_out` :1053,
`guess_VarRV_cond_uniform` :1420, `guess_joint_fdist_marginal` :792, unwrapped
one-liner `denote_run_*` lemmas :279–:291. `dsdp_simulator.v`: 7 statements
(:236–:483). `dsdp_entropy.v`: `dsdp_fiber_card` :200. `dsdp_game_derivation.v`:
`walk_obs_dsdp` :284.

### 2.3 Confirmed clean

`dsdp_convert.v`, `dsdp_symbolic_exec.v`, the whole `homomorphic_encryption/`
tree (except `indcpa_ror.v`'s missing `Set Implicit Arguments`, below), all
blueprint `.tex` node bodies. The counting sections of `dsdp_main.v`
(:163–:667) are clean thanks to existing `Let`/`Local Notation` layers.

### 2.4 Root causes

1. `indcpa_ror.v` is the only file on the DSDP chains without
   `Set Implicit Arguments` (every other `homomorphic_encryption/` and
   `dsdp/` file on the chain has it). All five heavy parameters of
   `indcpa_epsilon` (`indcpa_ror.v:241`) are implicit-derivable: `AHE`/`Renc`
   from `rand_of_renc : Renc -> rand AHE`, `index_renc` from
   `renc_card : #|Renc| = index_renc`, `t_msg` from `msg_of_chmsg`,
   `t_cipher` from `chcipher_of_cipher`. That is why every call spells 11
   arguments (12 sites in `dsdp_main.v` alone, ~110 lines). Definition-after-
   `End`-section is NOT the cause: `real_game_leak_S`
   (`dsdp_indcpa_advantage.v:409`) is also post-section with 14 binders yet
   is called with 8 args, because its file sets implicit arguments.
2. The `_leak_S` axis has no experiment/adversary records. The non-leaking
   axis has `dsdp_indcpa_experiment` (`dsdp_game_derivation.v:579`) and
   `dsdp_indcpa_adversary` (:678), which keep `dsdp_alice_view_advantage_le`'s
   LHS to one line; the guess/simulation axis falls back to raw parameter
   lists.
3. Recurring mid-level terms are unnamed: the trace
   `game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded …)`
   appears 14× (10 in `dsdp_main.v`, 4 in `dsdp_simulator.v`); the proof of
   `dsdp_alice_unpredictability_entropy_ge` opens with `set eps_sum := …`,
   inventing exactly the abbreviation its statement lacks.
4. Hand-written literals duplicated: the shared `GC_sample … GC_ret` literal
   at 8 sites in `dsdp_guess_fiber.v` (:719, :728, :757, :896, :989, :1224,
   :1296, :1519 — the last already named `Let view_distr`); a 4-line
   `AO_combine` block and a 3-line `AO_recv_output` term ×5 in
   `dsdp_game_derivation.v`. (`gc_eq` :298 carries a longer
   four-`card_msg`-sample variant that will NOT share the name.)
5. Loose section hypotheses discharge into positional argument lists
   (`dsdp_entropy.v`: arity 9–10 at `dsdp_main.v` call sites).

### 2.5 Proven in-repo remedies

`oracle_real_pkg`/`oracle_zero_pkg` wrappers (`dsdp_game_code.v:690,700`);
`dsdp_indcpa_experiment` + `dsdp_indcpa_adversary` records; `Let
guess_reduction` used inside headline statements (`dsdp_main.v:722`);
`dsdp_locs_disjoint` (`dsdp_simulator.v:225`) — audited to bundle EXACTLY
the three `fseparate` conditions of `dsdp_main.v:943-949`, no more, no
fewer; `real_game_leak_S`/`zero_game_leak_S`
(`dsdp_indcpa_advantage.v:409,423`); the `Let` chain of
`dsdp_entropy_trace.v` (both statements 2 lines).

## 3. Design

Statement-preservation invariant for all stages: every restated theorem
must state the same mathematical claim as before — identical up to `Let`
inlining, record-projection unfolding, binder promotion/reordering,
implicit-argument status, and hypothesis bundling into a
conjunction/record whose round-trip is proved. No hypothesis may be
strengthened or weakened.

### 3.0 Stage 0 — `Set Implicit Arguments` in `indcpa_ror.v`

One atomic commit: add `Set Implicit Arguments. Unset Strict Implicit.` to
`indcpa_ror.v`, adjust the 33 `indcpa_epsilon` call sites repo-wide
(`indcpa_ror.v` 11, `dsdp_main.v` 12, `dsdp_indcpa_advantage.v` 7,
`idealized/idealized_indcpa.v` 6, `dsdp_game_code.v` 6,
`dsdp_game_derivation.v` 2, `dsdp_simulator.v` 2 — mentions, of which the
epsilon applications shrink from 11 to 6 explicit args), plus any other
declarations in the file that gain implicits. Zero semantic risk; after this
commit, re-measure which multi-line argument blocks remain (input to the
§3.2 decision gate).

### 3.1 Stage 1 — headline Let layer

Files: `dsdp_main.v`, `dsdp_simulator.v`, `dsdp_indcpa_advantage.v`.

**`Section dsdp_alice_guess`** (`dsdp_main.v:673`), which already holds `Let
game / real_game / guess_reduction` (:712–:724):

- Promote `cipher_of_chcipher` and `chcipher_of_cipherK` from per-theorem
  binders (:750–:751, :795–:796, :862–:863) to section
  `Variable`/`Hypothesis`. (`dsdp_alice_guess_V2_zero_le` does not use
  them; default used-variables-only discharge applies — audited: no
  `Proof using` anywhere in scope.)
- Add (`eps` takes no adversary argument here because the reduction head is
  the section-level `Let guess_reduction`):
  - `Let dsdp_leak_S_trace := game_of_trace_seeded dsdp_weight_names
    (dsdp_alice_obs_leak_S_seeded card_msg card_renc).`
  - `Let hop_reduction (site : nat) := guess_reduction ∘
    denote_game_shim_leak_S renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher cipher_of_chcipher pkey_of_party msg_of_idx rand0
    seed (zero_hop_prefix site dsdp_leak_S_trace) site.`
  - `Let eps (site : nat) : R := indcpa_epsilon renc_card rand_of_renc
    msg_of_chmsg chcipher_of_cipher pkey_of_party (hop_reduction site).`
    (post-Stage-0 spelling)
  - `Let sdistr_success := guess_sdistr_success renc_card rand_of_renc
    chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed
    predictor.` and `Let sdistr_success_real := …_real ….` (names keep the
    `sdistr` discriminator: `guess_sdistr_success` vs `guess_fdist_success`
    are distinct quantities joined by `guess_success_sdistr_eq_fdist`)
  - `Let oracle_real_locs := locs (oracle_real_pkg renc_card rand_of_renc
    msg_of_chmsg chcipher_of_cipher pkey_of_party).` and
    `Let oracle_zero_locs := locs (oracle_zero_pkg renc_card rand_of_renc
    t_msg chcipher_of_cipher pkey_of_party).`
- Restate the four statements (:730, :749, :794, :861) with these names;
  rewrite the proofs to use them (the `le_trans` middle term of :794's
  proof and the `have Hzero` both collapse). The section hypothesis
  `predictor_locs_disj` (:695, against `protocol_state`) stays as-is.

Worked target shape for `dsdp_alice_guess_V2_real_le` (audited: the `Let`
bodies expand to exactly the current statement):

```coq
Theorem dsdp_alice_guess_V2_real_le
    (Hore : fseparate (locs predictor) oracle_real_locs)
    (Hoze : fseparate (locs predictor) oracle_zero_locs)
    (Hinj : injective (fun v : plain AHE => w_u3 * v)) :
  sdistr_success_real <= card_msg%:R^-1 + (eps 0 + eps 1).
```

`dsdp_alice_unpredictability_entropy_ge` becomes
`log card_msg%:R - log (1 + card_msg%:R * (eps 0 + eps 1)) <=
unpredictability_entropy` with `Let unpredictability_entropy :=
Hunp_leak_S …`.

**`Section dsdp_alice_indcpa`** (`dsdp_main.v:83`, non-leak axis): the same
device for `dsdp_alice_view_advantage_le` :131 — `Let` for the trace
`game_of_trace (corrupted_view dsdp_experiment)`, `Let hop_reduction_of
(A : raw_package) (site : nat)` over `denote_game_shim`, and
`Let eps_of (A : raw_package) (site : nat)`; the reduction head here is the
theorem-bound adversary, hence the extra argument.

**`Section dsdp_alice_simulation`** (`dsdp_main.v:915`): same `Let` set as
the guess section but with the adversary parameter (`eps A site` — the head
at :959/:967 is the theorem-bound `A` :941); promote `cipher_of_chcipher` /
`chcipher_of_cipherK` there too (:939-:940). The three `fseparate` binders
of :943-:949 are replaced by `dsdp_locs_disjoint` (exact-match audited;
this is hypothesis bundling under the extended invariant).

**`dsdp_simulator.v`**: same `eps A site`/trace `Let`s in the advantage
section for `dsdp_advantage_sim_le` :281 (its reduction head is
lambda-bound, :293 — the `Let` must abstract over it); promote the
`cipher_of_chcipher` pair (:282-:283) to the section.

**`dsdp_indcpa_advantage.v`** — placement per target, since the targets
straddle `Section dsdp_game_code_leak_S` (:155–:403):

- :272 / :318 / :363 (inside the section): section-local `Let`s for the
  `denote_game_leak_S` application, the epsilon argument block, and named
  oracle location sets.
- :69 (before the section) and :443 (after `End`): top-level abbreviation
  `Definition`s in the `real_game_leak_S`/`zero_game_leak_S` pattern
  (:409/:423) — with Stage-0 implicits these carry short explicit
  signatures; a section-local device cannot reach these two statements.

`Let`-semantics notes (audited): a definitional `Let` is zeta-inlined at
`End Section`, so discharged statements are unchanged; discharged types
carry beta-redexes like `((fun site => …) 0)`, which is why verification
uses a conversion test (§4), not a textual diff. A `Let` closed by `Qed`
discharges as an opaque `_subproof` constant instead
(`card_ffun_msg_subproof` precedent) — all Stage-1 `Let`s are definitional.
`dsdp_main.v` is apex (nothing `Require`s it), so display cost there is nil.

### 3.2 Stage 2 — `_leak_S` records; marshalling record behind a decision gate

- Add the missing `_leak_S` experiment record and adversary record
  (bundling the `fseparate` side conditions), mirroring
  `dsdp_indcpa_experiment`/`dsdp_indcpa_adversary`. Home:
  `dsdp_indcpa_advantage.v` (first `_leak_S` file on the import chain).
  Relation to the base record: PROJECT, not embed —
  `exp_card_randomness`/`exp_card_plaintext` feed the symbolic block and
  `exp_msg_of_index`'s dependent type, so embedding would force rewrites at
  every existing projection (audited).
- Marshalling record for `indcpa_epsilon` parameters: DECISION GATE after
  Stage 0. Build it only if the post-Stage-0 measurement still shows
  multi-line epsilon argument blocks dominating statements. Its residual
  win at `dsdp_indcpa_secrecy_le` is 10 of the 16 `P.(exp_…)` projection
  occurrences (:700-:716) — the `denote_game_shim` block needs 4 fields
  outside the marshalling set and is untouched either way. If built:
  compile-test must include `idealized_indcpa.v:143`
  (`rewrite /indcpa_epsilon` keys on the flat form and record projections
  are non-primitive — no `Set Primitive Projections` in any real source);
  field naming must resolve `index_renc` (`indcpa_ror.v:242`, deliberately
  an index per the file's Design Commitment 1) vs `exp_card_randomness`
  (`dsdp_game_derivation.v:583`).
- Rewire the Stage-1 `Let eps` bodies to record projections where records
  land; Stage-1 statements do not change (the `Let` layer absorbs the
  signature churn).
- New identifiers pass the SSProve-style adversarial naming audit before
  commit. Blueprint gains `def:` nodes for the new records (sibling of
  `def:secrecy_problem`) with `\rocq{}` links.

### 3.3 Stage 3 — literal naming, hypothesis bundling, blueprint graph

- `dsdp_guess_fiber.v`: name the shared `GC_sample … GC_ret` literal once,
  hoisted before its first use (:719), reused at the 8 sites and unifying
  with the existing `Let view_distr` (:1519 body); `gc_eq` :298 keeps its
  distinct four-sample variant — fix is line-wrapping plus the existing
  `output_term` notation (:304, currently defined after `gc_eq`; move it
  up); add `Local Notation guess_sig := (id_guess, (chProd (cipher_list
  t_cipher) t_msg, t_msg))` (Local because it mentions section variables;
  sweep both the `chProd …` and `… × …` spellings); `Let` for the constant
  `denote_run_caps 11 8 9 10 7 6 [::]` prefix (9-lemma family) and the
  `dsdp_output w_v1 w_u1 w_u2 w_u3` prefix; use the existing `Let drun` at
  the 3 bypass sites (:453, :482, :546); wrap the one-liner `denote_run_*`
  lemmas to ≤100 columns.
- `dsdp_game_derivation.v`: name the 4-line `AO_combine` block and the
  3-line `AO_recv_output` term as `Definition`s; reuse across
  `walk_obs_dsdp`, `walk_obs_dsdp_leak_S`, `obs_of_procs_dsdp`,
  `obs_of_procs_dsdp_leak_S`, `dsdp_alice_obs_leak_S_seeded`.
- `dsdp_game_code.v`: NO record dependency (records live downstream of this
  file — import-order makes that impossible; its in-section adversary
  binders are already short). Stage 0 shrinks its epsilon argument blocks;
  add an in-section `Let` for the residual shared block if it is still
  multi-line, else leave the four `advantage_*` lemmas as-is.
- `dsdp_entropy.v`: bundle the three primality hypotheses and the fiber
  prerequisites (`constraint_fiber_n`, `InputRV_proj_n`, `VarRV_uniform_n`,
  `VarRV_indep_inputs_n`, `joint_eq_input_n`) into record(s) with proved
  round-trips, dropping post-discharge arity at the
  `dsdp_main.v`/`dsdp_guess_fiber.v` call sites. Watch the opaque-`Let`
  precedent (`card_ffun_msg_subproof`).
- `dsdp_main.v:117`: `Example dsdp_experiment_hops` → `Lemma` (blueprint
  declares it a lemma; nothing depends on the kind).
- Blueprint graph repair (`blueprint/src/*.tex`) — all EIGHT duplicate
  node pairs, not just the two originally found:
  - `dsdp_alice_view_advantage_le`: `thm:alice_view_advantage`
    (`security.tex`) vs `thm:dsdp_secure` (`content.tex`) — make
    `security.tex` canonical, add the missing `\uses` edge (reach 2 → 31).
  - `thm:alice_guess_real` (`security.tex` bundle) vs
    `thm:guess_sdistr_success_le` / `lem:guess_advantage_le` /
    `thm:dsdp_alice_secrecy_leak_S` (`it_bound_bridge.tex`).
  - `Pr_dsdp_sol_uniform_ring`: `lem:exist_pr_sol` vs
    `lem:dsdp_fiber_uniform`; `dsdp_fiber_card_ring`:
    `lem:exist_fiber_card` vs `lem:dsdp_fiber_uniform`.
  - `lower_obs`: `def:lower_obs` vs `def:lower_obs_output`; `walk_obs`:
    `def:walk_obs` vs `def:walk_obs_output` (merge the `_output` variants).
  - Faithfulness branch: `content.tex:673-677` already documents the
    fixture as "a check on the derivation, not the object anything
    downstream uses" — so mark `lem:dsdp_faithful` and
    `cor:dsdp_advantage_derived` intentionally standalone via `%` comment
    (a `\uses` edge would misstate the dependency); give
    `lem:obs_of_procs_dsdp_leak_S` its real parent edge.
  - DROPPED (audit): adding `\rocq{}` links for `lem:dsdp_is_correct` /
    `lem:one_time_pad` — the `% library:` comments at `security.tex:71-73`
    and :375-378 are a documented decision; those modules are outside
    MODULES so coqdoc anchors would 404, and `lemma_3_5'`'s prime is not
    expressible in `ROCQ_NAME_RE`.

## 4. Verification and commit discipline

- Each stage splits into atomic tasks; each task: project build with the
  local switch (`~/Projects/coq/_opam`), rocq-auditor pre-commit, commit.
- Coverage ratchet: `blueprint/check_coverage.py` hard-fails on any new
  `Definition`/`Record`/`Example`→`Lemma` in a MODULES-scoped file without
  a `\rocq{}` node or an exclude line — and every file this spec touches is
  MODULES-scoped. Each stage's plan carries an explicit node-or-exclude
  budget for its new declarations (`Let`/`Notation` are exempt from the
  checker). Run the coverage check green per stage, in addition to
  `make_blueprint.sh` (which does NOT invoke the checker).
- Statement-preservation check per restated theorem: conversion test
  (`Goal <old statement> = <new statement>. reflexivity. Qed.` in a scratch
  file, or `Eval cbv beta zeta`), NOT a textual `About` diff — discharged
  `Let`s leave beta-redexes.
- Stage-2 records (if the gate passes): compile-test first as a minimal
  scratch file against the real switch, including the
  `idealized_indcpa.v:143` unfold-pattern casualty.
- Naming: strict snake_case, no semantic-stripping abbreviations (hence
  `sdistr_success`, keeping the discriminator); `eps` retained as the ε
  math-notation exception (header + blueprint use it; only clash repo-wide
  is a `Local Notation` in `robust/weightedmean.v`, different file);
  SSProve-extension identifiers pass the adversarial naming gate.

## 5. Risks and mitigations

- Stage-2 signature churn: absorbed by the Stage-1 `Let` indirection;
  call-site sweep enumerated in §3.0.
- `Let` opacity/unification: only definitional `Let`s are introduced; any
  `Let` that would close with `Qed` becomes a transparent `Definition`.
- Non-primitive record projections break `rewrite /indcpa_epsilon`-style
  proofs (`idealized_indcpa.v:143`): gated compile-test before the
  marshalling record is built.
- Proof-performance regressions on giant terms: abbreviation generally
  helps (the `eapply`-not-`apply:` and `set`-abstraction lessons from the
  SSProve work); verify with batch `coqc` timing where a proof was
  previously near a timeout.
- Blueprint node merges must keep `check_coverage.py` green (the merged
  node keeps the `\rocq{}` anchors of both).

## 6. Non-goals / deferred

- No renaming of existing theorem identifiers (headline names and blueprint
  `\rocq{}` anchors stay valid).
- No `\rocq{}` links into modules outside MODULES scope (documented
  `% library:` comments remain the mechanism).
- Off-chain same-disease neighbours are deferred with this note as the
  record: `core/dsdp_pismc.v` (missing `Set Implicit Arguments`;
  post-discharge arities 12–21 over ~30 statements) and
  `core/dsdp_program.v` (med). Not on any headline dependency chain.
- `du2002/`, `pgg-smc/`, and other trees outside the DSDP chains.

## 7. Open items for the implementation plan

- §3.2 decision gate: post-Stage-0 measurement criteria for building the
  marshalling record (proposed: build only if ≥3 statements still carry a
  ≥2-line epsilon argument block).
- If the marshalling record is built: field name for
  `index_renc`-vs-`exp_card_randomness`, and the exact field list.
- Final names for `eps` / `eps_of` / `hop_reduction` /
  `dsdp_leak_S_trace` / `unpredictability_entropy` after the naming audit.
- Order of restatement within Stage 1 so that each commit compiles
  (advantage lemma before real_le before entropy_ge).
- Node-or-exclude budget per stage for the coverage ratchet.
