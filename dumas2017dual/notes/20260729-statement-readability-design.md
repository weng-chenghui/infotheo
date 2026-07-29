# Statement-readability refactor — design spec (2026-07-29)

Approved scope: all three stages, plus blueprint dependency-graph repair.
Branch: `20260729-0028-reduction-form-security` (continue in place).

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
| `dsdp/simulation/dsdp_simulator.v` | `dsdp_advantage_sim_le` :281 (16 lines byte-identical with `dsdp_main.v`:957-972) |
| `dsdp/counting/dsdp_entropy.v` | `Pr_dsdp_sol_uniform` :237, `dsdp_centropy1_uniform` :262, `dsdp_centropy1_uniform_n` :679 (post-discharge arity 9–10 at call sites) |

### 2.2 Medium-severity targets (covered by the same abbreviations)

`dsdp_main.v`: `US_n_compromised_leaks_secret` :366, `dsdp_alice_guess_V2_zero_le`
:730. `dsdp_game_code.v`: `advantage_hop` :885, `advantage_le` :977,
`denote_game_shim_valid` :649. `dsdp_guess_fiber.v`: the `denote_run_caps`
family (8 statements, :479–:611), the `resolve (pack predictor) …` family
(6 statements), `guess_resolved_par` :362, `guess_inner_out` :1053,
`guess_VarRV_cond_uniform` :1420, `guess_joint_fdist_marginal` :792, unwrapped
one-liner `denote_run_*` lemmas :279–:291. `dsdp_simulator.v`: 8 statements
(:236–:483). `dsdp_entropy.v`: `dsdp_fiber_card` :200. `dsdp_game_derivation.v`:
`walk_obs_dsdp` :284.

### 2.3 Confirmed clean

`dsdp_convert.v`, `dsdp_symbolic_exec.v`, the whole `homomorphic_encryption/`
tree (except `indcpa_epsilon` placement), all blueprint `.tex` node bodies.
The counting sections of `dsdp_main.v` (:163–:667) are clean thanks to
existing `Let`/`Local Notation` layers.

### 2.4 Root causes

1. `indcpa_epsilon` is defined after `End indcpa_ror`
   (`homomorphic_encryption/indcpa_ror.v:241`), so all 10 scheme/marshalling
   parameters are explicit at every call; only the 11th (`reduction`) carries
   information. 12 call sites in `dsdp_main.v` alone (~110 lines).
2. The `_leak_S` axis has no experiment/adversary records. The non-leaking
   axis has `dsdp_indcpa_experiment` (`dsdp_game_derivation.v:579`) and
   `dsdp_indcpa_adversary` (:678), which keep `dsdp_alice_view_advantage_le`'s
   LHS to one line; the guess/simulation axis falls back to raw parameter
   lists.
3. Recurring mid-level terms are unnamed: the trace
   `game_of_trace_seeded dsdp_weight_names (dsdp_alice_obs_leak_S_seeded …)`
   appears 14×; the proof of `dsdp_alice_unpredictability_entropy_ge` opens
   with `set eps_sum := …`, inventing exactly the abbreviation its statement
   lacks.
4. Hand-written literals duplicated: a 10-line `GC_sample … GC_ret` literal
   ×5 in `dsdp_guess_fiber.v`; a 4-line `AO_combine` block and a 3-line
   `AO_recv_output` term ×5 in `dsdp_game_derivation.v`.
5. Loose section hypotheses discharge into positional argument lists
   (`dsdp_entropy.v`: arity 9–10 at `dsdp_main.v` call sites).

### 2.5 Proven in-repo remedies

`oracle_real_pkg`/`oracle_zero_pkg` wrappers (`dsdp_game_code.v:690,700`);
`dsdp_indcpa_experiment` + `dsdp_indcpa_adversary` records; `Let
guess_reduction` used inside headline statements (`dsdp_main.v:722`);
`dsdp_locs_disjoint` bundling three `fseparate` conditions
(`dsdp_simulator.v:225`); `real_game_leak_S`/`zero_game_leak_S`
(`dsdp_indcpa_advantage.v:409,423`); the `Let` chain of
`dsdp_entropy_trace.v` (both statements 2 lines).

## 3. Design

Statement-preservation invariant for all three stages: every discharged
theorem must state the same mathematical claim as before — identical up to
`Let` inlining, record-projection unfolding, and binder
promotion/reordering. No hypothesis may be strengthened or weakened.

### 3.1 Stage 1 — headline Let layer

Files: `dsdp_main.v`, `dsdp_simulator.v`, `dsdp_indcpa_advantage.v`.

In `Section dsdp_alice_guess` (`dsdp_main.v:673`), which already holds `Let
game / real_game / guess_reduction` (:712–:724):

- Promote `cipher_of_chcipher : t_cipher -> cipher AHE` and
  `chcipher_of_cipherK : cancel chcipher_of_cipher cipher_of_chcipher` from
  per-theorem binders (:750–:751, :795–:796, :862–:863) to section
  `Variable`/`Hypothesis`. (`dsdp_alice_guess_V2_zero_le` does not use them;
  discharge adds only used variables, so it is unaffected.)
- Add:
  - `Let dsdp_leak_S_trace := game_of_trace_seeded dsdp_weight_names
    (dsdp_alice_obs_leak_S_seeded card_msg card_renc).`
  - `Let hop_reduction (site : nat) := guess_reduction ∘
    denote_game_shim_leak_S renc_card rand_of_renc chmsg_of_msg
    chcipher_of_cipher cipher_of_chcipher pkey_of_party msg_of_idx rand0
    seed (zero_hop_prefix site dsdp_leak_S_trace) site.`
  - `Let eps (site : nat) : R := indcpa_epsilon AHE Renc card_renc renc_card
    rand_of_renc t_msg t_cipher msg_of_chmsg chcipher_of_cipher
    pkey_of_party (hop_reduction site).`
  - `Let guess_success := guess_sdistr_success renc_card rand_of_renc
    chmsg_of_msg chcipher_of_cipher pkey_of_party msg_of_idx rand0 seed
    predictor.` and `Let guess_success_real := …_real ….`
  - `Let oracle_real_locs := locs (oracle_real_pkg renc_card rand_of_renc
    msg_of_chmsg chcipher_of_cipher pkey_of_party).` and
    `Let oracle_zero_locs := locs (oracle_zero_pkg renc_card rand_of_renc
    t_msg chcipher_of_cipher pkey_of_party).`
- Restate the four statements of the section with these names; rewrite the
  proofs to use them (the `le_trans` middle term of :794's proof and the
  `have Hzero` both collapse). The existing section hypothesis
  `predictor_locs_disj` (:695, against `protocol_state`) is distinct from
  `Hore`/`Hoze` and stays as-is.

Worked target shape for `dsdp_alice_guess_V2_real_le`:

```coq
Theorem dsdp_alice_guess_V2_real_le
    (Hore : fseparate (locs predictor) oracle_real_locs)
    (Hoze : fseparate (locs predictor) oracle_zero_locs)
    (Hinj : injective (fun v : plain AHE => w_u3 * v)) :
  guess_success_real <= card_msg%:R^-1 + (eps 0 + eps 1).
```

`dsdp_alice_unpredictability_entropy_ge` becomes
`log card_msg%:R - log (1 + card_msg%:R * (eps 0 + eps 1)) <= Hunp` with
`Let Hunp := Hunp_leak_S …`. Note `Hunp` is currently also the *hypothesis
naming* convention; final name passes the naming gate (candidate:
`Let unpredictability_entropy := Hunp_leak_S …`).

`Section dsdp_alice_simulation` (`dsdp_main.v:915`) gets the same `Let` set
(its own clone), erasing the 16-line byte-duplicate with
`dsdp_simulator.v:290-305`; the three `fseparate` binders of :938 are
replaced by the existing `dsdp_locs_disjoint` (exactly the three conditions
it bundles — matching `dsdp_advantage_sim_le`'s use).

`dsdp_simulator.v`: same `eps`/`hop_reduction`/trace abbreviations in its
advantage section (as `Let`s), shortening `dsdp_advantage_sim_le` :281.

`dsdp_indcpa_advantage.v`: downstream files reference this file's lemmas, so
use section-local `Definition` (not `Let`) for the abbreviations —
`Definition`s survive discharge as named constants (the
`real_game_leak_S`/`zero_game_leak_S` precedent) and keep downstream call
sites short too. Targets: an `eps`-analogue over its section parameters, a
trace name, and named oracle location sets for the `fseparate` binders of
:272/:318/:363/:443 and :69.

`Let`-semantics note: a `Let` is inlined at `End Section`, so discharged
statements are unchanged; `dsdp_main.v` is the apex file (no downstream), so
display cost is nil there.

### 3.2 Stage 2 — record root-cause layer

- `indcpa_ror.v`: introduce a marshalling record bundling the 10 fixed
  parameters (`AHE`, `Renc`, `card_renc`, `renc_card`, `rand_of_renc`,
  `t_msg`, `t_cipher`, `msg_of_chmsg`, `chcipher_of_cipher`,
  `pkey_of_party`; candidate name `indcpa_marshalling`). Change
  `indcpa_epsilon` to take the record + `reduction`. Aggressive cleanup: no
  11-arg compatibility form; every call site follows (files:
  `dsdp_game_code.v`, `dsdp_game_derivation.v`, `dsdp_indcpa_advantage.v`,
  `dsdp_main.v`, `dsdp_simulator.v`, `idealized/idealized_indcpa.v`).
- Add the missing `_leak_S` experiment record (embedding
  `dsdp_indcpa_experiment` as a field plus the `seed : denv` datum; no field
  duplication) and a `_leak_S` adversary record bundling the `fseparate`
  side conditions, mirroring `dsdp_indcpa_adversary`. Home:
  `dsdp_indcpa_advantage.v` (the first `_leak_S` file on the import chain).
- Shorten `dsdp_indcpa_secrecy_le`'s 11 `P.(exp_…)` projections via the
  marshalling record (a `marshalling_of_experiment` projection).
- Rewire the Stage-1 `Let eps` bodies to record projections; statements from
  Stage 1 do not change (this is why Stage 1 goes first: the `Let` layer
  absorbs the signature churn).
- New identifiers pass the SSProve-style adversarial naming audit before
  commit. Blueprint gains `def:` nodes for the new records (sibling of
  `def:secrecy_problem`) with `\rocq{}` links.

### 3.3 Stage 3 — literal naming, hypothesis bundling, blueprint graph

- `dsdp_guess_fiber.v`: name the 10-line `GC_sample … GC_ret` literal once,
  hoisted before its first use (:716), reused at the 5 sites and unifying
  with the existing `Let view_distr` (:1517); rewrap `gc_eq` :298 using the
  existing `output_term` notation (:304 — currently defined after `gc_eq`;
  move it up); add `Notation guess_sig := (id_guess, (chProd (cipher_list
  t_cipher) t_msg, t_msg))`; `Let` for the constant `denote_run_caps 11 8 9
  10 7 6 [::]` prefix and the `dsdp_output w_v1 w_u1 w_u2 w_u3` prefix; use
  the existing `Let drun` at the 3 bypass sites (:453, :482, :546); wrap the
  one-liner `denote_run_*` lemmas to ≤100 columns.
- `dsdp_game_derivation.v`: name the 4-line `AO_combine` block and the
  3-line `AO_recv_output` term as `Definition`s; reuse across
  `walk_obs_dsdp`, `walk_obs_dsdp_leak_S`, `obs_of_procs_dsdp`,
  `obs_of_procs_dsdp_leak_S`, `dsdp_alice_obs_leak_S_seeded`.
- `dsdp_game_code.v`: the repeated 2-line `indcpa_epsilon` argument block
  and the 5-line adversary binder block (:886, :929, :978, :1076) are
  resolved by Stage 2's records; restate the four `advantage_*` lemmas
  accordingly.
- `dsdp_entropy.v`: bundle the three primality hypotheses and the fiber
  prerequisites (`constraint_fiber_n`, `InputRV_proj_n`, `VarRV_uniform_n`,
  `VarRV_indep_inputs_n`, `joint_eq_input_n`) into record(s), dropping
  post-discharge arity at the `dsdp_main.v`/`dsdp_guess_fiber.v` call
  sites. Watch the opaque-`Let` unification precedent
  (`card_ffun_msg_subproof`).
- Blueprint graph repair (`blueprint/src/*.tex`):
  - Merge the duplicate `dsdp_alice_view_advantage_le` nodes
    (`thm:alice_view_advantage` in `security.tex` vs `thm:dsdp_secure` in
    `content.tex`): keep both environments but make `security.tex` the
    canonical statement node and add the missing `\uses` edge so the
    31-node derivation is reachable from it; same treatment for
    `thm:alice_guess_real` vs the three `it_bound_bridge.tex` nodes.
  - Connect the faithfulness branch (`lem:dsdp_faithful`,
    `cor:dsdp_advantage_derived`, `lem:obs_of_procs_dsdp*`,
    `def:dsdp_alice_obs`, `def:walk_obs_output`) to the headline chains via
    `\uses`, or mark it intentionally standalone in a `%` comment.
  - Add missing `\rocq{}` links: `lem:dsdp_is_correct` →
    `dsdp_correctness.dsdp_is_correct` / `dsdp_entropy_trace.dsdp_result_correct`;
    `lem:one_time_pad` → `spp_proba.lemma_3_5'`; note `def:party_views` as
    section-local (`Let`) and therefore not coqdoc-addressable.
  - Fix the declaration-kind mismatch of `lem:dsdp_experiment_hops`
    (`Example` in code).

## 4. Verification and commit discipline

- Each stage splits into atomic tasks; each task: project build with the
  local switch (`~/Projects/coq/_opam`), rocq-auditor pre-commit, commit.
- Stage 2's new `indcpa_epsilon` signature is compile-tested first as a
  minimal scratch file against the real switch before the plan is executed.
- Statement-preservation check per restated theorem: `Check`/`About` of the
  discharged statement compared against the pre-refactor form.
- Blueprint edits verified with `blueprint/make_blueprint.sh`.
- Naming: strict snake_case, no semantic-stripping abbreviations; `eps`
  retained as the ε math-notation exception (header + blueprint use it);
  SSProve-extension identifiers pass the adversarial naming gate.

## 5. Risks and mitigations

- Stage-2 signature churn: absorbed by the Stage-1 `Let`/`Definition`
  indirection; call-site sweep enumerated in 3.2.
- `Let` opacity/unification: `dsdp_entropy.v` has the
  `card_ffun_msg_subproof` precedent; any new opaque `Let` that appears in a
  unifiable position is made a transparent `Definition` instead.
- Proof-performance regressions on giant terms: abbreviation generally
  helps (the `eapply`-not-`apply:` and `set`-abstraction lessons from the
  SSProve work); verify with batch `coqc` timing where a proof was
  previously near a timeout.
- Blueprint node merges must not break `check_coverage.py` /
  `blueprint-exclude.txt` expectations; run the coverage check after.

## 6. Non-goals / deferred

- No renaming of existing theorem identifiers (headline names and blueprint
  `\rocq{}` anchors stay valid).
- Off-chain same-disease neighbours are deferred with this note as the
  record: `core/dsdp_pismc.v` (missing `Set Implicit Arguments`;
  post-discharge arities 12–21 over ~30 statements) and
  `core/dsdp_program.v` (med). Not on any headline dependency chain.
- `du2002/`, `pgg-smc/`, and other trees outside the DSDP chains.

## 7. Open items for the implementation plan

- Exact field list and name of the marshalling record; whether
  `dsdp_indcpa_experiment` itself should embed it (single source of truth)
  or carry a projection.
- Final names for `eps` / `hop_reduction` / `dsdp_leak_S_trace` /
  `unpredictability_entropy` after the naming audit.
- Order of restatement within Stage 1 so that each commit compiles
  (advantage lemma before real_le before entropy_ge).
