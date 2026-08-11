# Plan: MonodromyProfile end-to-end evaluation (probe-first)

Date: 2026-08-11

Request: `docs/superpowers/requests/2026-08-11-monodromy-profile-end-to-end-ROCQ-formalization-request.md`
Response target: `docs/superpowers/requests/2026-08-11-monodromy-profile-end-to-end-ROCQ-formalization-response.md`
Probe directory: `docs/superpowers/probes/2026-08-11-monodromy-profile-end-to-end/`

Scope: this plan executes the EVALUATION only. No permanent `.v` file and no paper
source changes. The implementation plan is a separate later artifact, written only
after the user has reviewed the response and selected a design (request section 12).

How this instantiates `rocq-probe-first-spec`: the request document already carries
the claim ledger (section 10) and soundness invariants (section 9), so skill step 1
is done by the requester. The recon below is the precedent grep (step 3, partial).
The probe schedule is step 2. The two adversarial audits are step 3. Folding
findings into the response document is step 4. Step 5 (implementation plan) is
explicitly out of scope pending user design selection.

## 1. Recon: request citations verified against the live tree (2026-08-11)

All named `.vo` files are FRESH (newer than their `.v`), checked file-by-file:
`pgg_monodromy_profile`, `pgg_run`, `card_exchange_pismc`, `pgg_input_commitment`,
`input_encoding`, `covering_scheme`, `pgl27_run`, `pgl27_profile`, `pgl27_trace`,
`five_card_family`, `kim_run`, `den_boer_run`, `denboer_trace`, `smc_interpreter`.
Probes can `Require Import` everything with zero dependency builds.

| Request claim | Verified at | Status |
|---|---|---|
| `MonodromyProfile R` fields `mp_M/mp_secretT/mp_PI/mp_security/mp_plug` | `pgg-smc/protocol/pgg_monodromy_profile.v:49-55` | exact match |
| `run_party`, `run_verifier`, `run_recover` | same file, lines 73, 76, 81-83 | exact match |
| `profile_eps/k/anonymous/private`, `profile_recon_encode` | same file, lines 87-110 | exact match |
| `dealer_with_input_encoding` needs `content_of`, `W`, `inputs`, `players`, `P_idx` | `pgg-smc/protocol/pgg_run.v:45-51` | match; NOTE: lives in `pgg_run.v`, not `card_exchange_pismc.v` |
| `endpoints_of_trace` generic | `pgg-smc/protocol/pgg_run.v:60-61` (+ `sheets_of`, `evens`, `identity_deck`) | match |
| `run_interp` | `smc/smc_interpreter.v:89` | match |
| PGL instance run artifacts `pgl27_fuel/players/dealer_run/saprocs/procs` | `pgg-smc/instances/pgl27/pgl27_run.v:51-117` | match; fuel = 220, players = explicit 8-element list |
| PGL end-to-end bridges proved manually | `pgl27_run.v:119-233` (`pgl27_run_terminates`, `pgl27_verifier_endpoints`, `pgl27_endpoints`, `pgl27_endpoints_size`, `pgl27_run_recovers`, `run_recover_pgl27`, `run_party_pgl27`) | match |
| Count bridge absent from profile | current mechanism is `tcast (pgl27_endpoints_size s w0)` at `pgl27_run.v:183,221` — a per-instance proved size equation plus cast | confirmed |
| Five-card carrier | `five_card_profile (R) (eps) Hlt Hgt Hspec L : MonodromyProfile R` at `pgg-smc/instances/kim2025/five_card_family.v:164-169`; den Boer member at `eps = 0` | match; carrier requires THREE side-condition proofs (see section 2) |
| `ie_output_correct` cut-permuted, not executed-trace | `pgg-smc/reconstruct/input_encoding.v:47` | match |
| Instances define own trace functions | `pgl27_trace.v:318,414,477,581,638,703`; `denboer_trace.v:141`; `kim_trace.v:39` | match |
| Trace keystone | `trace_secrecy_of_view` in `pgg-smc/security/pgg_trace_secrecy.v` | match |

Corrections and additional live evidence the probes must use:

1. **File correction.** The generic dealer helper and endpoint extractor are in
   `pgg-smc/protocol/pgg_run.v`, not `card_exchange_pismc.v`.
2. **Name drift.** `five_card_family.v:27,159` reference `five_card_eps0_perfect`;
   the landed lemma is `five_card_eps0_eq0` (same file, line ~180). Probes cite the
   latter.
3. **Duplication precedent already landed.** `kim_procs := den_boer_procs`
   (`kim_run.v:28`) and `kim_player_trace := denboer_player_trace R`
   (`kim_trace.v:39`). The probe-7.3 requirement (changing the shuffle witness
   requires no new process definition) has a landed instance-level precedent; the
   probe shows the generic adapter preserves it.
4. **Player-list computability constraint is documented in source.**
   `pgl27_run.v:53-56`: a concrete list rather than `enum 'I_8` was chosen so
   `fold_senv` reduces under `vm_compute`. Probe P-G measures this rather than
   discovering it.
5. **Distribution precedents.** Exact: `pgl27P : R.-fdist (bool * pgg_gT pgl27_M)`
   (`pgl27_secrecy.v:60`); all-decks and per-deck: `pgl27P_alldecks`, `pgl27P_deck`
   (`pgl27_trace.v:463,628`); finite-word generalized: `pgl27P_gen`,
   `pgl27P_word_gen` (`pgl27_word_privacy.v:74,80`); five-card: `dbP`
   (`denboer_trace.v`). Probe P-F states its typed definitions against these shapes.
6. **Import DAG (relevant edges).** `pgg_run.v` imports `card_exchange_pismc` +
   `pgg_input_commitment` and does NOT import `pgg_monodromy_profile`;
   `pgg_monodromy_profile.v` imports `card_exchange_pismc` + `pgg_reconstruct`
   modules and does NOT import `pgg_run`. Instance run files import both. A new
   adapter module in `pgg-smc/protocol/` importing both has no cycle risk; P-G
   verifies mechanically.
7. **No name collision.** `ExecutableProfile` does not occur in any `.v` or plan
   file. Probes still use a probe-local record name (section 3, P-C) so no
   permanent naming decision is smuggled in; the naming audit proposes the final
   name.
8. **Probe conventions.** Probe `.v` sources are committed (gate passes on them,
   see commits `d18003cc`, `4b99b83f`, `aafcc92c`), `.vo` outputs are gitignored,
   compile via a `rebuild.sh` clone using the `_CoqProject` `-R` flags (lines
   259-268), one worker, mutations in separate files with expected errors recorded
   in `MUTATIONS.md` (2026-08-10 convention).

## 2. Pinned carriers

Both carriers keep `R : realType` abstract (the weakest structure every instance
uses; no probe may specialize `R`).

**PGL carrier.**

```coq
Variable R : realType.
(* carrier *)   Check pgl27_profile R : MonodromyProfile R.
(* runtime *)   Variables (s : bool) (w0 : pgg_gT pgl27_M).
(* existing run artifacts to compare against, statement-level *)
(* pgl27_fuel = 220, pgl27_players (concrete 8-list), pgl27_procs s w0 *)
```

**Five-card carrier (den Boer member, eps = 0).**

```coq
Variable R : realType.
(* side conditions at eps = 0, shapes verbatim from five_card_eps0_eq0 *)
Hypothesis Hlt0  : (0:R) < 5%:R^-1.
Hypothesis Hgt0  : - (4%:R * 5%:R^-1) < (0:R).
Hypothesis Hspec0 : `|(0:R)| < 4%:R / 5%:R.
Variable L : nat.
Check five_card_profile Hlt0 Hgt0 Hspec0 L : MonodromyProfile R.
(* runtime *)  Variables (a b : bool) (w0 : pgg_gT FiveCardKim_M) (P_idx : nat).
```

The probe prelude also proves the three side conditions concretely (they hold at
0; if `ltr0n`/`invr_gt0`-style one-liners stall past the stopping rule, keep them
as section hypotheses and record that in the response — they are model
parameters, not evaluation subjects). The Kim member (`eps <> 0`) is exercised in
P-D only through the shuffle-witness-invariance comparison.

Count-bridge concrete values: PGL `pi_T' pgl27_PI = 7` vs `ts_T' orbit_scheme`
(8 players / 8 shares); five-card `pi_T' FiveCardKim_PI = 4` vs
`ts_T' fcI_scheme` (5 players / 5 shares). P-B confirms both equalities compute.

## 3. Probe schedule

Strictly sequential (single rocqworker, per project rules). Each probe is one
`rocq-prover` subagent launch (`model: opus`), statements written by the
orchestrator, iteration by the agent, results re-verified by the orchestrator
(`rocq_compile_file` + `rocq_assumptions`).

| ID | File | Request § | Carrier(s) | Pass condition | Mutation check | Budget |
|---|---|---|---|---|---|---|
| P-A | `probe_a_sufficiency.v` | 7.1 | generic `mp : MonodromyProfile R`, then both concrete | Compiles; the section-Variable register is exactly the data the profile cannot supply | drop any one register Variable → compile fails | 60 turns, ≤2 full compiles |
| P-B | `probe_b_count_bridge.v` + `probe_b_mutation.v` | 7.4 | both | generic endpoint-decoder through an explicit equality field, instantiated at both carriers with computed equalities | mismatched probe-local profile (4-share scheme against 8-player PI) fails; error recorded in `MUTATIONS.md` | 40 turns |
| P-C | `probe_c_pgl27_exec.v` | 7.2 | PGL | probe-local adapter record instantiated; `adapter_procs = pgl27_procs s w0` proved at statement level; termination/endpoints/recovery transported | change adapter fuel field to 1 → termination transport fails | 60 turns |
| P-D | `probe_d_fivecard_exec.v` | 7.3 | five-card (den Boer + Kim witness) | same adapter record instantiated with commit prologue; `adapter_procs = den_boer_procs a b w0 P_idx` statement-level; Kim-witness instance yields definitionally the same processes | change `ep_inputT` to unit → commit prologue fails to typecheck | 80 turns |
| P-E | `probe_e_traces.v` | 7.5 | both | generic participant-trace, coalition-trace, verifier-endpoint extractors typecheck at both carriers; generic endpoint equation instantiated via existing instance lemmas, Qed | wrong process index (dealer id for verifier id) → equation unprovable, isolated in mutation section | 60 turns |
| P-F | `probe_f_distributions.v` | 7.6 | PGL exact + PGL finite-word | typed sample space / distribution / trace-RV / pushforward definitions compile against `pgl27P`, `pgl27P_word_gen`, `dbP` shapes; profile-supplied vs model-parameter split tabulated | none (typing probe; mutation meaningless) | 60 turns |
| P-G | `probe_g_depgraph.sh` + `probe_g_vmcompute.v` | 7.7 | PGL | script proves proposed placement acyclic from live `Require` lines; `Time vm_compute` comparison enum-vs-concrete-list recorded | none (measurement probe) | 40 turns |
| P-H | `probe_h_adapter_decomposition.v` | 6.1/6.2 + headline | both | decomposition: headline (terminates + endpoint size + recovery through the adapter) derived to Qed from Admitted supports; separate section instantiates a 6.1-style extended record at both carriers for field-count/migration comparison | drop the count-bridge field from the record → headline underivable | 80 turns |

Probe-order rationale: P-A produces the missing-data register that every later
probe and all three design-alternative verdicts consume, and it alone settles the
literal target. P-B is the highest type-level risk and is cheap. P-C/P-D exercise
the two families against the landed process lists. P-E/P-F stack traces and
distributions on top. P-G needs the placement candidate that P-A..P-F converge
on. P-H is last because its field list is P-A's register refined by B..G.

### P-A construction detail (the register method)

Open a section over `mp : MonodromyProfile R` and attempt request-7.1 items 1-8
in order (dealer, participant list, verifier, session-typed process list, erased
list, `run_interp` result, one participant trace, verifier endpoints). Every value
the profile cannot supply is introduced as an explicitly-tagged section Variable
(the register): expected from recon — `content_of`, shuffle word/deck `W`, input
identifiers, concrete player list, `P_idx`, fuel. Facts that are obligations
rather than data (termination) are recorded as stated-but-not-provable-generically
in a comment block and carried to P-H as Admitted supports. The register, not
prose, is the response's section-12.9 list. Then close the section and instantiate
at both carriers to prove the register is fillable.

### P-C/P-D adapter shape (decided now, probe-local name `EPP`)

```coq
Record EPP (R : realType) (mp : MonodromyProfile R) := MkEPP {
  ep_inputT   : Type ;                                   (* run argument: PGL bool, five-card bool*bool *)
  ep_count    : pi_T' (mp_PI mp) = ts_T' (rp_scheme (mp_plug mp)) ; (* count bridge, P-B design *)
  ep_players  : seq 'I_(pi_T' (mp_PI mp)).+1 ;           (* concrete, for vm_compute; see recon 4 *)
  ep_players_eq : ep_players = enum 'I_(pi_T' (mp_PI mp)).+1 ;
  ep_fuel     : nat ;
  ep_dealer   : ep_inputT -> pgg_gT (mp_M mp) -> (* session-typed dealer via dealer_with_input_encoding *) _ ;
  ep_procs    : ep_inputT -> pgg_gT (mp_M mp) -> _ ;     (* dealer ++ verifier ++ players, erased *)
}.
```

The `_` placeholders are the session-type/process types the probe pins during
elaboration (they are what P-A discovers; writing them here without compiling
would violate this skill). The input-mode decision is: one adapter record, input
mode carried by `ep_inputT` plus the dealer field; committed-input instances put
the commit prologue inside `ep_dealer`, empty-input instances use the empty
prologue — this mirrors the landed degeneration
(`exchange_dealer_with_commit_nil`) and keeps the two modes distinct in the
public interface via the dealer construction, not via a hidden flag. If
elaboration forces two constructors instead, that is a P-C/P-D finding, folded
into the response, not a plan failure.

### Admitted policy

Request 9.1 bans `Admitted` in permanent sources; request 13.7 bans
`Axiom`/`Parameter`/`Abort` in probes; request 13.8 requires every miniature used
as positive evidence to end in `Qed`. Reading adopted: `Admitted` is legal in
probe files ONLY for P-H decomposition supports, whose provability is never
claimed; every other probe is Qed-only. `rocq_assumptions` output is recorded per
probe in the response.

## 4. Execution protocol

- **Compile command**: clone of
  `docs/superpowers/probes/2026-08-08-pgl27-orbit-split/rebuild.sh` — `rocq
  compile -q` with the `_CoqProject` `-R` flags (`-R . infotheo`, the five
  `pgg-smc/* pgg_smc` mappings, `-R pgg-smc/reconstruct pgg_reconstruct`, plus
  the needed instance dirs), one worker, never `make -j>1`, never concurrent
  compilation.
- **Agent launch preamble** (every `rocq-prover` launch, per project CLAUDE.md):
  1. Dependency status: "all imports pre-built and fresh as of 2026-08-11 recon;
     do not rebuild any permanent file."
  2. Exact line ranges: the recon table above supplies file:line for every cited
     object; each launch quotes the rows it needs.
  3. Section context: the pinned-carrier blocks of section 2, verbatim.
  4. Budget statement: the per-probe budget from the schedule table; use
     `rocq_check`/`rocq_step_multi` for all intermediate testing.
  5. Four-phase rocq-mcp workflow reminder (`rocq_start` → `rocq_query` →
     `rocq_check`/`rocq_step_multi` → apply once to the probe file).
  Plus standing constraints: no `rewrite !` with arithmetic lemmas; no `lia`;
  `run_interp`/`vm_compute` goals follow the abstract-leaves recipe (abstract
  explosive leaves — perms, enum, decode — into section Variables so
  `vm_compute` stays atomic, then instantiate); never let `done`/`//` see
  table-shaped terms (premise-first side conditions); `Show` to inspect goals;
  `apply:`/`exact` with space.
- **Stopping rule** (per probe row): after two failed attempts on the same claim,
  stop editing; write the smallest isolating counter-probe. Counter-probe fails →
  the claim is false: mark the ledger row NO-GO, keep the counter-probe as
  evidence. Counter-probe succeeds → the probe was wrong: fix it and record what
  misled, verbatim, in the response.
- **Strategy-switch discipline**: global CLAUDE.md rule is in force for every
  agent; the orchestrator treats a reported switch as a hard interrupt.
- **Never delete probe files.** Commit probe sources; `.vo` stays gitignored.

## 5. Adversarial audits (after P-A..P-H, both launched in one message)

| Audit | Agent | Compile rights | Remit |
|---|---|---|---|
| Soundness | `general-purpose` | YES — owns the single rocqworker | Each of the 12 soundness invariants (request section 9) checked against probes and response draft; verdict-derivation validity (section 6 below); quantifier order explicit in every proposed theorem; run/trace/trace-function/trace-distribution distinction maintained; `Fail`-tactic tautology probes and a vacuity instantiation of the P-H hypothesis set |
| Naming and precedent | `mathcomp-skills:mathcomp-style-auditor` | NO — read-only, to keep one worker | Proposed public names vs repo conventions: `run_` prefix is reserved for executing artifacts, record projections take a noun prefix (`profile_*` precedent); every claimed precedent verified at a live path; collision sweep for the final record name; statement comments are terse mathematical descriptions per the H-series grammar |

Both receive: the request, this plan, all probe files, the response draft, and
repo read access. Both must return explicit GO / NO-GO with per-finding
machine-checked evidence. Every finding is folded into the response document
(accepted → changed claim; rejected → recorded reason); nothing is answered in a
side document.

## 6. Verdict discipline and response assembly

**Literal target**: GO iff P-A completes all eight constructions with an EMPTY
register (nothing supplied beyond the profile and natural runtime values `s`/`(a,b)`
and `w0`). Recon predicts NO-GO (the dealer alone needs `content_of`, `W`,
`players`, `P_idx` — none are profile fields), but the verdict is copied from the
compiled register, not from this prediction.

**Layered target**: GO iff (i) P-C and P-D instantiate the same adapter record at
both carriers with statement-level process equality against the landed lists,
(ii) P-B's count bridge computes at both carriers and its mutation fails,
(iii) P-H's headline reaches Qed, and (iv) P-G shows an acyclic placement and a
recorded `vm_compute` verdict. Anything less is NO-GO with the failing probe cited.

Response section map (request section 12) — every row cites compiled evidence:

| Response item | Source |
|---|---|
| 1 literal verdict | P-A register |
| 2 layered verdict | P-B, P-C, P-D, P-G, P-H |
| 3 gap matrix | P-A register + recon table, one row per request-section-5 gap |
| 4 proposed interfaces | P-H record definitions (both 6.1-style and 6.2-style), verbatim |
| 5 probe paths, build commands, results | probe dir + `rebuild.sh` + per-probe `rocq_assumptions` |
| 6 module dependency analysis | P-G script output |
| 7 proof obligations at both carriers | P-H Admitted-support list + P-C/P-D transported lemmas |
| 8 migration-impact table | P-C/P-D statement-level equalities (statements unchanged ⇒ migration is re-plumbing); field-count comparison from P-H section 2 |
| 9 remaining instance-specific data | P-A register minus adapter fields |
| 10 paper-safe claim | strongest claim supported by compiled probes only |
| 11 recommendation among 6.1/6.2/6.3 | P-H comparison + P-A bundle-arity measurement for 6.3 |
| 12 scope estimate | stage table drafted from probe outcomes |

Evaluation questions Q1-Q12 (request section 8) map: Q1,Q2 ← P-A; Q3 ← P-G+P-H;
Q4 ← P-C+P-D; Q5 ← P-A/P-H `ep_procs`; Q6 ← P-C/P-D fuel fields + P-G; Q7 ← P-E;
Q8 ← P-F; Q9,Q10 ← P-F + security-layer recon (5); Q11 ← P-C/P-D statement-level
equalities; Q12 ← verdicts + audits.

## 7. Stages and estimates

| Stage | Work | Estimate |
|---|---|---|
| A (done) | Recon, carrier pinning, this plan | done 2026-08-11 |
| B | P-A..P-H sequential probe runs | 8 agent launches, dominated by P-D/P-H; expect 1-2 days wall-clock with review between launches |
| C | Two audits, one message | half a day including fold-back |
| D | Response assembly + probe commit through the gate | half a day |
| E | User review; design selection | user-gated; no implementation before it |

Commit points: probes + `MUTATIONS.md` + `rebuild.sh` in one commit at end of
stage B (gate runs on probe `.v`; match the committed-probe comment style; if
Stage 2 fails on infrastructure, dispatch a real auditor agent per skill step 8 —
no `--no-verify`); response + plan updates at end of stage D.

## 8. Risk register

| Risk | Signal | Mitigation (decided now) |
|---|---|---|
| Generic `enum`-based player list kills `vm_compute` | P-G timing or elaboration failure | Adapter keeps concrete `ep_players` field + `ep_players_eq` proof; this is the design, not a fallback — source comment `pgl27_run.v:53-56` already documents the constraint |
| Session-type elaboration rejects the unified dealer field | P-C or P-D elaboration failure | Split `ep_dealer` into two constructors (committed / empty input) inside the SAME record; record the split as a finding; the two modes stay distinct publicly either way |
| Count bridge not expressible as one equality field | P-B failure at either carrier | Fall back to the landed per-instance mechanism (proved size equation + `tcast`) as an adapter FIELD (`ep_endpoints_size`); mutation check still applies |
| `vm_compute` termination proofs explode at five-card commit prologue | P-D timeout | Abstract-leaves recipe; reuse `den_boer_run_terminates` by transport across the statement-level process equality instead of re-running `vm_compute` |
| Audit Stage 2 silent no-op or token cap at probe commit | S996/S998 sentinel in gate output | Dispatch `mathcomp-skills:mathcomp-style-auditor` on the probe files as the missing review, then commit; log if bypass is ever used |
| Probe iteration diverges | two failures on one row | Stopping rule (section 4); counter-probe decides claim-false vs probe-wrong |

## 9. Completion checklist (mirrors request section 13)

- [ ] Literal and layered verdicts separate, each citing its probe
- [ ] Both carriers' probes compiled with one worker
- [ ] P-B mutation fails as intended, error text recorded
- [ ] P-G placement acyclic
- [ ] Runs / traces / trace functions / trace distributions distinguished throughout
- [ ] `git status` clean on permanent `.v` and paper sources
- [ ] No `Axiom` / `Parameter` / `Abort` in any probe; `Admitted` only in P-H supports
- [ ] Every positive-evidence miniature Qed, `rocq_assumptions` recorded
- [ ] Response names all data beyond `MonodromyProfile` (P-A register verbatim)
- [ ] Paper claim matches the strongest compiled interface
- [ ] Both audits returned explicit verdicts; findings folded into the response
- [ ] Probe files committed, never deleted
