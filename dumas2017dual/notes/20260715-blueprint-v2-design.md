# Blueprint v2: the SMC-DSDP security analysis

Date: 2026-07-15
Status: design, pending adversarial audit
Supersedes: `dumas2017dual/blueprint` (to become `blueprint_v1`)

## 1. Problem

The blueprint at `dumas2017dual/blueprint` no longer describes what
`dumas2017dual/dsdp/dsdp_main.v` proves.

Measured, not asserted:

- `dsdp_main.v` declares 17 `prf` roots (15 headline theorems + 2 supporting
  lemmas `BobView_indep_V1` / `CharlieView_indep_V1`).
- The blueprint gives `\rocq` nodes to 3 of the 15 headlines:
  `dsdp_alice_view_advantage_le`, `dsdp_alice_guess_ideal_le`,
  `dsdp_alice_guess_real_le`.
- `python3 dumas2017dual/blueprint/check_coverage.py` currently exits non-zero:
  `FAIL code=349 blueprint=38 excl=306 (refs into scope=39)`, with
  `bob_privacy_V3`, `charlie_privacy_V2`, `dsdp_alice_simulation_secure`,
  `dsdp_alice_view_statdist_le` uncovered.
- `blueprint-exclude.txt` still waives `relay_privacy_n` and
  `guess_sdistr_success_real`, both deleted in commits c76b1f34 and a9cb400f.
  Waiving a nonexistent declaration is silent.

The structural mismatch is larger than the coverage gap. The current document is
titled "The Auto-Derivation Chain" and is organised as a machinery pipeline:
symbolic model, derived view, lowering, denotation, hybrid ladder, control
record, DSDP instance. That is a document about how the game is constructed. The
required document is about what an adversary learns, with each headline theorem
chaining from `dsdp_main.v` to its leaves. Different spine, different document.

## 2. Decisions

Settled during brainstorming; each is load-bearing for what follows.

**D1 — Threat-model spine.** Parts group by who is corrupted. Chapter = one
headline theorem, chained to leaves.

**D2 — Library leaves, hypotheses surfaced.** Chains descend until they reach an
Infotheo / MathComp / SSProve library fact, which is cited as a black box. Every
in-tree declaration on a chain gets a real node. Each chapter opens with a
standing-hypotheses block, so an over-hypothesised or vacuous bound is visible
on the page.

**D3 — Chain-walker checker, no exclusion list.** Scope is defined as the claim
rather than as a file list. `blueprint-exclude.txt` is deleted.

**D4 — Simulation scope stated, worst-case scoped as a blue node.** The two
simulation headlines are average-case. The chapter says so, and carries one blue
conjecture node for the worst-case statement.

## 3. Why D3: the exclusion list is implicated in the drift

`check_coverage.py` scopes itself to the 10 `.v` files in `make_blueprint.sh`'s
`MODULES`, regex-extracts every declaration, and requires each to have a `\rocq`
node or a line in `blueprint-exclude.txt`. The blueprint documents 38 of 349
declarations in that scope, so 306 waivers exist purely to reconcile a too-wide
scope with a narrow claim. The instrument checks 12% of what it claims to cover.

Three concrete failures, all live today:

1. **It conflates two meanings.** `dsdp_game_code:push_val` is plumbing that
   should never be a node: a legitimate permanent waiver.
   `dsdp_main:dsdp_centropy_uniform` is an undocumented headline: a real gap.
   Both are one line in one file. When the headline was appended, the checker
   went quiet about the largest hole in the document. The drift travelled
   through the waiver list.
2. **It invents declarations.** `CTOR_RE` reads ssreflect tactic brackets as
   `Inductive` constructors, minting a phantom declaration `exact` from
   `dsdp_main.v:793` and `:830` (`| exact: A_disj_state | ...`). The checker
   demands the blueprint document a theorem that does not exist; the in-design
   remedy is another waiver.
3. **Waivers go stale silently.** Two exist today (§1).

### The replacement

Scope becomes the claim: *every headline theorem in `dsdp_main.v` has a chapter,
and every declaration on its proof chain has a node.*

- **Roots**: `prf` lines in `dsdp_main.glob` (17 today, enumerated in §4).
- **Chain**: transitive walk of `R` reference lines across the referenced
  modules' `.glob` files.
- **Scope**: the union of the chains. Everything else is out of scope by
  construction. Nothing to waive; nothing to go stale.
- **Failures**: a root with no chapter; a chain node with no `\rocq` node; a
  `\rocq` ref resolving to no `def`/`prf`.

Verified feasible before adopting. `dsdp_main.glob` records 17 `prf` and 3105
`R` lines. Attributing `R` lines to the byte span of `dsdp_alice_guess_real_le`
recovers exactly its real chain — `dsdp_alice_guess_ideal_le` and
`dsdp_alice_guess_advantage_le` (the two triangle legs) joined via
`guess_advantage_eq` — matching the proof body at `dsdp_main.v:748-774`.

The same walk yields each theorem's section variables (`dsdp_alice_guess.seed`,
`.predictor`, `.w_u3`, `.msg_of_idx`, …), which are the D2 hypothesis blocks.
Generating rather than transcribing them removes a staleness channel.

Self-maintaining properties: deleting a theorem removes its chain from scope;
adding one puts its whole chain under the ratchet; renaming surfaces as dangling
as it does today; ssreflect syntax is never parsed, so no phantom `exact`.

Secondary confirmation: the untracked probe files `probe_p3_statdist.v` and
`probe_p5_skeletons.v` define competing `statdist` and `adv_sim_le`
declarations. A file-list scope needs fresh waivers for them. The chain-walker
excludes them automatically, because no headline chain references them.

## 4. The document

Title: **SMC-DSDP: A Machine-Checked Security Analysis**.

### Part 0 — Foundations

1. The DSDP protocol, the party views, the threat models.
2. The derivation machinery. Re-framed from v1 `content.tex`.
3. The output-exposing extension. Re-framed from v1 `it_bound_bridge.tex`.

These stay pipeline-shaped; that is the natural shape for machinery. Parts I-III
follow the chapter template and cite back.

### Part I — Corrupted Alice, semi-honest

| Ch | Theorem | Statement |
|----|---------|-----------|
| 4  | `dsdp_centropy_uniform` | `H(V2,V3 \| view) = log m` |
| 5  | `dsdp_centropy_uniform_n` | `H(V \| view) = log (m^n)` [N-party] |
| 6  | `dsdp_alice_view_advantage_le` | `AdvantageE <= 2 * epsilon_cpa` |
| 7  | `dsdp_alice_guess_ideal_le` | `guess <= 1/card_msg` |
| 8  | `dsdp_alice_guess_advantage_le` | `AdvantageE <= 2 * epsilon_cpa` |
| 9  | `dsdp_alice_guess_real_le` | `guess <= 1/card_msg + 2 * epsilon_cpa` |
| 10 | `dsdp_alice_unpredictability_ge` | `H_unp >= log m - log (1 + 2 m eps)` |
| 11 | `dsdp_alice_simulation_secure` | `AdvantageE real (Sim ∘ Ideal) <= 2 * eps` |
| 12 | `dsdp_alice_view_statdist_le` | `statdist <= 2 * epsilon_cpa` |

### Part II — Corrupted relay

| Ch | Theorem | Statement |
|----|---------|-----------|
| 13 | `bob_privacy_V1`, `charlie_privacy_V1` | `H(V1 \| RelayView) = log m > 0` |
| 14 | `bob_privacy_V3` | `H(V3 \| BobView) = log m > 0` |
| 15 | `charlie_privacy_V2` | `H(V2 \| CharlieView) = log m > 0` |

Chapter 13 pairs the two symmetric theorems; they share the supporting lemmas
`BobView_indep_V1` and `CharlieView_indep_V1`, which are nodes within it.

### Part III — Malicious Alice

| Ch | Theorem | Statement |
|----|---------|-----------|
| 16 | `US_n_compromised_leaks_secret` | `H(VS_0 \| View) = 0` [N-party] |
| 17 | `US_compromised_leaks_V2` | `H(V2 \| View) = 0` |

Part III is the negative result: a malicious Alice fixing her query to `e_1`
reads a relay's input off her view. It belongs in the security story precisely
because it bounds what Parts I-II can claim.

## 5. Chapter template

```
Ch N   <plain-language title>
       THEOREM  <rocq name>   <statement>

 N.0   Scope and standing hypotheses     [generated from the glob walk]
 N.1   The statement                     [\rocq -> dsdp_main]
 N.2   <chain step>                      -> N.3, N.4
 ...
 N.k   Leaves reached
         <local decl>       [module]        node
         <library fact>     [SSProve]       black box
         enc_ind_cpa_real_or_zero           ASSUMPTION
```

Node bodies follow the mathcomp-qbs statement-comment standard: a declarative
statement of what the object is, plus the formal statement. Proof strategy and
rationale go in `%` source comments, never in a rendered body.

## 6. Node status convention

- Green with `\rocq` link: proved, in-tree.
- Green without link, carrying a `% library:` comment: library fact cited as a
  black box. This is v1's existing convention (`lem:exist_pr_code`,
  `def:relational_advantage`).
- **ASSUMPTION**: `enc_ind_cpa_real_or_zero`, the single cryptographic
  assumption the document rests on.
- **Blue**: exactly one node, the worst-case simulation conjecture at 11.6.

## 7. The simulation chapter (D4)

The conversion logic exists and is sound. Verified before designing around it:

- `dsdp_simulator_factorization` (`dsdp_simulator.v:236`) proves
  `zero_game_leak_S ≈₀ dsdp_simulator_pkg ∘ dsdp_ideal_pkg` — perfect, no
  epsilon, `Qed`.
- The chain is: `real ≈(2eps) zero` (`dsdp_advantage_derived_leak_S`), then
  `zero ≈₀ Sim ∘ Ideal` (the factorization), joined by triangle into
  `dsdp_alice_simulation_secure` (`dsdp_main.v:842`). Packaged generically via
  `adv_sim_le_from_endpoint` (`smc/ssprove_ext_simulator.v:52`).
- The simulator is a genuine simulator: `sim_view_body` takes
  `run_ideal : raw_code 'unit`, so the ideal run returns nothing. The view is
  fabricated from `enc pk 0` plus fresh samples. `v2`, `v3`, `S` have no path
  in — a type-level witness, not a prose claim.
- `grep -cE '^(Admitted|Axiom|Parameter)'` returns 0 for `dsdp_simulator.v`,
  `ssprove_ext_simulator.v`, `ssprove_ext_statdist.v`.

**The gap the chapter must state.** Both simulation headlines are average-case:
`v2`, `v3` are sampled uniformly in-game, by `real_game_leak_S` on one side and
by `dsdp_ideal_pkg` on the other. Standard simulation security quantifies over
all inputs: for every input vector, real is indistinguishable from `Sim ∘ Ideal`.
This proves the uniform average. Chapter 11.0 states the departure and 11.6
carries the worst-case statement as a blue conjecture node, so the dependency
graph shows the frontier rather than implying it away.

## 8. Tooling changes

- `check_coverage.py` — rewritten as the §3 chain-walker. Emits hypothesis
  blocks as a generated `.tex` include.
- `blueprint-exclude.txt` — deleted.
- `make_blueprint.sh` — `MODULES` gains `dumas2017dual/dsdp/simulation/dsdp_simulator.v`,
  `smc/ssprove_ext_simulator.v`, `smc/ssprove_ext_statdist.v`. All three are
  absent today, so the simulation chapters' `\rocq` buttons would 404, and the
  current checker would stay silent because it skips refs into unscoped modules
  (`if lname not in declared: continue`).
- `COVERAGE.md` — rewritten for the chain-walker model.
- `git-hooks/pre-commit-blueprint-coverage` — retargeted at the new blueprint;
  `blueprint_v1` is dropped from the hook and from the build.

## 9. Risks

- **Glob walk filtering.** Raw output mixes qualified section variables
  (`dsdp_alice_guess.predictor`) with binder noise (`v:318`,
  `cipher_of_chcipher:314`). Needs a real filter, not a regex guess.
- **Transitive walk presupposes a full build.** Every referenced module's
  `.glob` must exist and be current. A stale `.glob` yields a wrong scope.
- **Chain size is unknown until walked.** ~150 nodes is an estimate from the
  38-node v1 plus the uncovered surface, not a measurement. Walk first, then
  size the writing.
- **Prose is the bulk of the work**, and it is the part no tool checks.
- **`A_disj_state` passed twice** (`dsdp_main.v:872`,
  `dsdp_simulator.v:299`) is read here as correct: `≈₀` raises one
  location-disjointness obligation per side and both sides' locs are
  `protocol_state`. Inferred from the package definitions, not machine-checked.
  Confirm during execution.
- **v1 reuse is a re-framing, not a copy.** `content.tex` chapters are ordered
  as a pipeline argument; dropping them into Part 0 needs new connective prose
  and re-pointed cross-references.
